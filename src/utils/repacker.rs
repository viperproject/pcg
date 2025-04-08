// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    borrow_pcg::coupling_graph_constructor::BorrowCheckerInterface,
    rustc_interface::{
        borrowck::{PoloniusOutput, RegionInferenceContext},
        data_structures::fx::FxHashSet,
        index::{bit_set::BitSet, Idx},
        middle::{
            mir::{
                tcx::PlaceTy, BasicBlock, Body, HasLocalDecls, Local, Mutability,
                Place as MirPlace, PlaceElem, ProjectionElem,
            },
            ty::{TyCtxt, TyKind},
        },
        target::abi::FieldIdx,
    },
};

use crate::rustc_interface::mir_dataflow;

use crate::{
    borrow_pcg::region_projection::PcgRegion,
    pcg::{PCGUnsupportedError, PcgError},
};

use super::Place;

#[derive(Debug, Clone, Copy)]
pub enum ProjectionKind {
    Ref(Mutability),
    RawPtr(Mutability),
    Box,
    Field(FieldIdx),
    ConstantIndex(ConstantIndex),
    Other,
}

pub struct ShallowExpansion<'tcx> {
    pub(crate) target_place: Place<'tcx>,

    /// Other places that could have resulted from this expansion. Note: this
    /// vector is always incomplete when projecting with `Index` or `Subslice`
    /// and also when projecting a slice type with `ConstantIndex`!
    pub(crate) other_places: Vec<Place<'tcx>>,
    pub(crate) kind: ProjectionKind,
}

impl<'tcx> ShallowExpansion<'tcx> {
    pub(crate) fn new(
        target_place: Place<'tcx>,
        other_places: Vec<Place<'tcx>>,
        kind: ProjectionKind,
    ) -> Self {
        Self {
            target_place,
            other_places,
            kind,
        }
    }

    pub(crate) fn base_place(&self) -> Place<'tcx> {
        self.target_place.last_projection().unwrap().0
    }

    pub fn expansion(&self) -> Vec<Place<'tcx>> {
        let mut expansion = self.other_places.clone();
        self.kind
            .insert_target_into_expansion(self.target_place, &mut expansion);
        expansion
    }
}

impl ProjectionKind {
    pub(crate) fn is_box(self) -> bool {
        matches!(self, ProjectionKind::Box)
    }

    pub(crate) fn insert_target_into_expansion<'tcx>(
        self,
        target: Place<'tcx>,
        expansion: &mut Vec<Place<'tcx>>,
    ) {
        match self {
            ProjectionKind::Field(field_idx) => {
                expansion.insert(field_idx.index(), target);
            }
            _ => {
                expansion.push(target);
            }
        }
    }
}

#[derive(Copy, Clone)]
pub struct CompilerExtra<'a, 'tcx> {
    #[allow(unused)]
    pub(crate) region_infer_ctxt: &'a RegionInferenceContext<'tcx>,
    #[allow(unused)]
    pub(crate) polonius_output: Option<&'a PoloniusOutput>,
}

#[derive(Copy, Clone)]
pub struct CompilerCtxt<'a, 'tcx, 'bc, T = &'bc dyn BorrowCheckerInterface<'a, 'tcx>> {
    pub(super) mir: &'a Body<'tcx>,
    pub(super) tcx: TyCtxt<'tcx>,
    pub(crate) bc: T,
    _marker: std::marker::PhantomData<&'bc ()>,
}

impl<'a, 'tcx, 'bc, T: BorrowCheckerInterface<'a, 'tcx> + ?Sized>
    CompilerCtxt<'a, 'tcx, 'bc, &'bc T>
{
    pub fn as_dyn(self) -> CompilerCtxt<'a, 'tcx, 'bc> {
        CompilerCtxt {
            mir: self.mir,
            tcx: self.tcx,
            bc: self.bc.as_dyn(),
            _marker: std::marker::PhantomData,
        }
    }
}

impl<'a, 'tcx, T> CompilerCtxt<'a, 'tcx, '_, T> {
    pub fn new(mir: &'a Body<'tcx>, tcx: TyCtxt<'tcx>, bc: T) -> Self {
        Self {
            mir,
            tcx,
            bc,
            _marker: std::marker::PhantomData,
        }
    }

    pub fn body(self) -> &'a Body<'tcx> {
        self.mir
    }

    pub fn tcx(self) -> TyCtxt<'tcx> {
        self.tcx
    }

    pub fn bc(&self) -> T
    where
        T: Copy,
    {
        self.bc
    }
}

impl CompilerCtxt<'_, '_, '_> {
    pub(crate) fn is_arg(self, local: Local) -> bool {
        local.as_usize() != 0 && local.as_usize() <= self.mir.arg_count
    }

    /// Returns `true` iff the edge from `from` to `to` is a back edge.
    pub(crate) fn is_back_edge(&self, from: BasicBlock, to: BasicBlock) -> bool {
        self.mir.basic_blocks.dominators().dominates(to, from)
            && self.mir.basic_blocks[from]
                .terminator()
                .successors()
                .any(|s| s == to)
    }

    pub fn num_args(self) -> usize {
        self.mir.arg_count
    }

    pub fn local_count(self) -> usize {
        self.mir.local_decls().len()
    }

    #[rustversion::before(2024-12-14)]
    pub fn always_live_locals(self) -> BitSet<Local> {
        mir_dataflow::storage::always_storage_live_locals(self.mir)
    }

    #[rustversion::since(2024-12-14)]
    pub fn always_live_locals(self) -> BitSet<Local> {
        mir_dataflow::impls::always_storage_live_locals(self.mir)
    }

    pub fn always_live_locals_non_args(self) -> BitSet<Local> {
        let mut all = self.always_live_locals();
        for arg in 0..self.mir.arg_count + 1 {
            // Includes `RETURN_PLACE`
            all.remove(Local::new(arg));
        }
        all
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct ConstantIndex {
    pub(crate) offset: u64,
    pub(crate) min_length: u64,
    pub(crate) from_end: bool,
}

pub(crate) struct DeepExpansion<'tcx>(Vec<ShallowExpansion<'tcx>>);

impl<'tcx> DeepExpansion<'tcx> {
    pub(crate) fn new(expansions: Vec<ShallowExpansion<'tcx>>) -> Self {
        Self(expansions)
    }

    pub(crate) fn other_expansions(&self) -> FxHashSet<Place<'tcx>> {
        self.0
            .iter()
            .flat_map(|e| e.other_places.iter())
            .cloned()
            .collect()
    }

    pub(crate) fn expansions(&self) -> &[ShallowExpansion<'tcx>] {
        &self.0
    }
}

impl<'tcx, 'bc> Place<'tcx> {
    pub fn to_rust_place<C: Copy>(
        self,
        repacker: CompilerCtxt<'_, 'tcx, 'bc, C>,
    ) -> MirPlace<'tcx> {
        MirPlace {
            local: self.local,
            projection: repacker.tcx.mk_place_elems(self.projection),
        }
    }

    /// Subtract the `to` place from the `self` place. The
    /// subtraction is defined as set minus between `self` place replaced
    /// with a set of places that are unrolled up to the same level as
    /// `to` and the singleton `to` set. For example,
    /// `expand(x.f, x.f.g.h)` is performed by unrolling `x.f` into
    /// `{x.g, x.h, x.f.f, x.f.h, x.f.g.f, x.f.g.g, x.f.g.h}` and
    /// subtracting `{x.f.g.h}` from it, which results into (`{x.f, x.f.g}`, `{x.g, x.h,
    /// x.f.f, x.f.h, x.f.g.f, x.f.g.g}`). The result contains the chain of
    /// places that were expanded along with the target to of each expansion.
    #[allow(clippy::type_complexity)]
    pub(crate) fn expand(
        mut self,
        to: Self,
        repacker: CompilerCtxt<'_, 'tcx, 'bc>,
    ) -> Result<DeepExpansion<'tcx>, PcgError> {
        assert!(
            self.is_prefix(to),
            "The minuend ({self:?}) must be the prefix of the subtrahend ({to:?})."
        );
        let mut expanded = Vec::new();
        while self.projection.len() < to.projection.len() {
            let ShallowExpansion {
                target_place,
                other_places,
                kind,
            } = self.expand_one_level(to, repacker)?;
            expanded.push(ShallowExpansion::new(target_place, other_places, kind));
            self = target_place;
        }
        Ok(DeepExpansion::new(expanded))
    }

    /// Expand `self` one level down by following the `guide_place`.
    /// Returns the new `self` and a vector containing other places that
    /// could have resulted from the expansion.
    pub fn expand_one_level(
        self,
        guide_place: Self,
        repacker: CompilerCtxt<'_, 'tcx, 'bc>,
    ) -> Result<ShallowExpansion<'tcx>, PcgError> {
        let index = self.projection.len();
        assert!(
            index < guide_place.projection.len(),
            "self place {:?} is not a prefix of guide place {:?}",
            self,
            guide_place
        );
        let new_projection = repacker.tcx.mk_place_elems_from_iter(
            self.projection
                .iter()
                .copied()
                .chain([guide_place.projection[index]]),
        );
        let new_current_place = Place::new(self.local, new_projection);
        let (other_places, kind) = match guide_place.projection[index] {
            ProjectionElem::Field(projected_field, _field_ty) => {
                let other_places = self.expand_field(Some(projected_field.index()), repacker)?;
                (other_places, ProjectionKind::Field(projected_field))
            }
            ProjectionElem::ConstantIndex {
                offset,
                min_length,
                from_end,
            } => {
                let range = if from_end {
                    1..min_length + 1
                } else {
                    0..min_length
                };
                assert!(range.contains(&offset));
                let other_places = range
                    .filter(|&i| i != offset)
                    .map(|i| {
                        repacker
                            .tcx
                            .mk_place_elem(
                                self.to_rust_place(repacker),
                                ProjectionElem::ConstantIndex {
                                    offset: i,
                                    min_length,
                                    from_end,
                                },
                            )
                            .into()
                    })
                    .collect();
                (
                    other_places,
                    ProjectionKind::ConstantIndex(ConstantIndex {
                        offset,
                        min_length,
                        from_end,
                    }),
                )
            }
            ProjectionElem::Deref => {
                let typ = self.ty(repacker);
                let kind = match typ.ty.kind() {
                    TyKind::Ref(_, _, mutbl) => ProjectionKind::Ref(*mutbl),
                    TyKind::RawPtr(_, mutbl) => ProjectionKind::RawPtr(*mutbl),
                    _ if typ.ty.is_box() => ProjectionKind::Box,
                    _ => unreachable!(),
                };
                (Vec::new(), kind)
            }
            ProjectionElem::Index(..)
            | ProjectionElem::Subslice { .. }
            | ProjectionElem::Downcast(..)
            | ProjectionElem::OpaqueCast(..) => (Vec::new(), ProjectionKind::Other),
            ProjectionElem::Subtype(_) => todo!(),
        };
        for p in other_places.iter() {
            assert!(
                p.projection.len() == self.projection.len() + 1,
                "expanded place {:?} is not a direct child of {:?}",
                p,
                self,
            );
        }
        Ok(ShallowExpansion::new(new_current_place, other_places, kind))
    }

    /// Expands a place `x.f.g` of type struct into a vector of places for
    /// each of the struct's fields `{x.f.g.f, x.f.g.g, x.f.g.h}`. If
    /// `without_field` is not `None`, then omits that field from the final
    /// vector.
    pub fn expand_field(
        self,
        without_field: Option<usize>,
        repacker: CompilerCtxt<'_, 'tcx, 'bc>,
    ) -> Result<Vec<Self>, PcgError> {
        let mut places = Vec::new();
        let typ = self.ty(repacker);
        if !matches!(typ.ty.kind(), TyKind::Adt(..)) {
            assert!(
                typ.variant_index.is_none(),
                "We have assumed that only enums can have variant_index set. Got {typ:?}."
            );
        }
        match typ.ty.kind() {
            TyKind::Adt(def, substs) => {
                let variant = typ
                    .variant_index
                    .map(|i| def.variant(i))
                    .unwrap_or_else(|| def.non_enum_variant());
                if let Some(without_field) = without_field {
                    assert!(without_field < variant.fields.len());
                }
                for (index, field_def) in variant.fields.iter().enumerate() {
                    if Some(index) != without_field {
                        let field = FieldIdx::from_usize(index);
                        let field_place = repacker.tcx.mk_place_field(
                            self.to_rust_place(repacker),
                            field,
                            field_def.ty(repacker.tcx, substs),
                        );
                        places.push(field_place.into());
                    }
                }
                if without_field.is_some() {
                    assert!(places.len() == variant.fields.len() - 1);
                } else {
                    assert!(places.len() == variant.fields.len());
                }
            }
            TyKind::Tuple(slice) => {
                if let Some(without_field) = without_field {
                    assert!(without_field < slice.len());
                }
                for (index, arg) in slice.iter().enumerate() {
                    if Some(index) != without_field {
                        let field = FieldIdx::from_usize(index);
                        let field_place =
                            repacker
                                .tcx
                                .mk_place_field(self.to_rust_place(repacker), field, arg);
                        places.push(field_place.into());
                    }
                }
                if without_field.is_some() {
                    assert!(places.len() == slice.len() - 1);
                } else {
                    assert!(places.len() == slice.len());
                }
            }
            TyKind::Closure(_, substs) => {
                for (index, subst_ty) in substs.as_closure().upvar_tys().iter().enumerate() {
                    if Some(index) != without_field {
                        let field = FieldIdx::from_usize(index);
                        let field_place = repacker.tcx.mk_place_field(
                            self.to_rust_place(repacker),
                            field,
                            subst_ty,
                        );
                        places.push(field_place.into());
                    }
                }
            }
            TyKind::Ref(..) => {
                places.push(
                    repacker
                        .tcx
                        .mk_place_deref(self.to_rust_place(repacker))
                        .into(),
                );
            }
            TyKind::Alias(..) => {
                return Err(PcgError::unsupported(
                    PCGUnsupportedError::ExpansionOfAliasType,
                ));
            }
            _ => unreachable!("ty={:?} ({self:?})", typ),
        }
        Ok(places)
    }
}

impl<'tcx, 'bc> Place<'tcx> {
    pub fn ty<C: Copy>(self, repacker: CompilerCtxt<'_, 'tcx, 'bc, C>) -> PlaceTy<'tcx> {
        (*self).ty(repacker.mir, repacker.tcx)
    }

    #[allow(unused)]
    pub(crate) fn get_ref_region(
        &self,
        repacker: CompilerCtxt<'_, 'tcx, 'bc>,
    ) -> Option<PcgRegion> {
        match self.ty(repacker).ty.kind() {
            TyKind::Ref(region, ..) => Some((*region).into()),
            _ => None,
        }
    }

    pub(crate) fn projects_shared_ref(self, repacker: CompilerCtxt<'_, 'tcx, 'bc>) -> bool {
        self.projects_ty(
            |typ| {
                typ.ty
                    .ref_mutability()
                    .map(|m| m.is_not())
                    .unwrap_or_default()
            },
            repacker,
        )
        .is_some()
    }

    pub(crate) fn projects_ty(
        self,
        mut predicate: impl FnMut(PlaceTy<'tcx>) -> bool,
        repacker: CompilerCtxt<'_, 'tcx, 'bc>,
    ) -> Option<Place<'tcx>> {
        self.projection_tys(repacker)
            .find(|(typ, _)| predicate(*typ))
            .map(|(_, proj)| {
                let projection = repacker.tcx.mk_place_elems(proj);
                Self::new(self.local, projection)
            })
    }

    pub(crate) fn projection_tys(
        self,
        repacker: CompilerCtxt<'_, 'tcx, 'bc>,
    ) -> impl Iterator<Item = (PlaceTy<'tcx>, &'tcx [PlaceElem<'tcx>])> {
        let mut typ = PlaceTy::from_ty(repacker.mir.local_decls()[self.local].ty);
        self.projection.iter().enumerate().map(move |(idx, elem)| {
            let ret = (typ, &self.projection[0..idx]);
            typ = typ.projection_ty(repacker.tcx, *elem);
            ret
        })
    }
}
