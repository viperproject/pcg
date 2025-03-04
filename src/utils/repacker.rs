// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use itertools::Itertools;
use rustc_interface::{
    data_structures::fx::FxHashSet,
    index::{bit_set::BitSet, Idx},
    middle::{
        mir::{
            tcx::PlaceTy, BasicBlock, Body, HasLocalDecls, Local, Mutability, Place as MirPlace,
            PlaceElem, ProjectionElem,
        },
        ty::{TyCtxt, TyKind},
    },
    mir_dataflow,
    target::abi::FieldIdx,
};

use crate::{
    borrow_pcg::region_projection::PCGRegion,
    combined_pcs::{PCGError, PCGUnsupportedError},
    rustc_interface,
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
    pub(crate) fn is_shared_ref(self) -> bool {
        matches!(self, ProjectionKind::Ref(Mutability::Not))
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
pub struct PlaceRepacker<'a, 'tcx: 'a> {
    pub(super) mir: &'a Body<'tcx>,
    pub(super) tcx: TyCtxt<'tcx>,
}

impl<'a, 'tcx: 'a> PlaceRepacker<'a, 'tcx> {
    pub fn new(mir: &'a Body<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        Self { mir, tcx }
    }

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

    pub fn body(self) -> &'a Body<'tcx> {
        self.mir
    }

    pub fn tcx(self) -> TyCtxt<'tcx> {
        self.tcx
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct ConstantIndex {
    pub(crate) offset: u64,
    pub(crate) min_length: u64,
    pub(crate) from_end: bool,
}

#[derive(Debug)]
pub struct ExpandStep<'tcx> {
    pub(crate) base_place: Place<'tcx>,
    pub(crate) projected_place: Place<'tcx>,
    pub(crate) kind: ProjectionKind,
}

impl<'tcx> ExpandStep<'tcx> {
    pub(crate) fn new(from: Place<'tcx>, to: Place<'tcx>, kind: ProjectionKind) -> Self {
        Self {
            base_place: from,
            projected_place: to,
            kind,
        }
    }
}

impl<'tcx> Place<'tcx> {
    pub(crate) fn to_rust_place(self, repacker: PlaceRepacker<'_, 'tcx>) -> MirPlace<'tcx> {
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
    /// x.f.f, x.f.h, x.f.g.f, x.f.g.g}`). The first vector contains the chain of
    /// places that were expanded along with the target to of each expansion.
    #[allow(clippy::type_complexity)]
    pub(crate) fn expand(
        mut self,
        to: Self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Result<(Vec<ExpandStep<'tcx>>, Vec<Self>), PCGError> {
        assert!(
            self.is_prefix(to),
            "The minuend ({self:?}) must be the prefix of the subtrahend ({to:?})."
        );
        let mut place_set = Vec::new();
        let mut expanded = Vec::new();
        while self.projection.len() < to.projection.len() {
            let ShallowExpansion {
                target_place,
                other_places,
                kind,
            } = self.expand_one_level(to, repacker)?;
            expanded.push(ExpandStep::new(self, target_place, kind));
            place_set.extend(other_places);
            self = target_place;
        }
        Ok((expanded, place_set))
    }

    /// Try to collapse all places in `from` by following the
    /// `guide_place`. This function is basically the reverse of
    /// `expand`.
    pub fn collapse(
        self,
        from: FxHashSet<Self>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Vec<ExpandStep<'tcx>> {
        let mut collapsed = Vec::new();
        let mut guide_places = vec![self];
        while let Some(place) = guide_places.pop() {
            let mut next_projection_candidates: Vec<Place<'tcx>> = from
                .iter()
                .copied()
                .filter(|p| place.is_strict_prefix(*p))
                .sorted_by_key(|p| p.projection.len())
                .collect();
            while let Some(next_candidate) = next_projection_candidates.pop() {
                let (expanded, new_places) = place.expand(next_candidate, repacker).unwrap();

                // Don't consider unpacking with targets in `new_places` since they are going
                // to be packed via the packing in `expanded`
                next_projection_candidates.retain(|p| !new_places.contains(p));

                collapsed.extend(expanded);
                guide_places.extend(new_places);
            }
        }
        collapsed.reverse();
        collapsed
    }

    /// Expand `self` one level down by following the `guide_place`.
    /// Returns the new `self` and a vector containing other places that
    /// could have resulted from the expansion.
    pub fn expand_one_level(
        self,
        guide_place: Self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Result<ShallowExpansion<'tcx>, PCGError> {
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
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Result<Vec<Self>, PCGError> {
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
                return Err(PCGError::unsupported(
                    PCGUnsupportedError::ExpansionOfAliasType,
                ));
            }
            _ => unreachable!("ty={:?} ({self:?})", typ),
        }
        Ok(places)
    }
}

impl<'tcx> Place<'tcx> {
    pub fn ty(self, repacker: PlaceRepacker<'_, 'tcx>) -> PlaceTy<'tcx> {
        (*self).ty(repacker.mir, repacker.tcx)
    }

    #[allow(unused)]
    pub(crate) fn get_ref_region(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Option<PCGRegion> {
        match self.ty(repacker).ty.kind() {
            TyKind::Ref(region, ..) => Some((*region).into()),
            _ => None,
        }
    }

    pub(crate) fn projects_shared_ref(self, repacker: PlaceRepacker<'_, 'tcx>) -> bool {
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
        repacker: PlaceRepacker<'_, 'tcx>,
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
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> impl Iterator<Item = (PlaceTy<'tcx>, &'tcx [PlaceElem<'tcx>])> {
        let mut typ = PlaceTy::from_ty(repacker.mir.local_decls()[self.local].ty);
        self.projection.iter().enumerate().map(move |(idx, elem)| {
            let ret = (typ, &self.projection[0..idx]);
            typ = typ.projection_ty(repacker.tcx, *elem);
            ret
        })
    }

    pub(crate) fn mk_place_elem(
        self,
        elem: PlaceElem<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Self {
        let elems = repacker
            .tcx
            .mk_place_elems_from_iter(self.projection.iter().copied().chain([elem]));
        Self::new(self.local, elems)
    }
}
