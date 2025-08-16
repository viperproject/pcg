// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::collections::BTreeMap;

use serde_derive::Serialize;

use crate::{
    borrow_checker::BorrowCheckerInterface,
    borrow_pcg::borrow_pcg_expansion::PlaceExpansion,
    owned_pcg::RepackGuide,
    pcg::{DataflowStmtPhase, EvalStmtPhase, ctxt::AnalysisCtxt},
    pcg_validity_assert,
    rustc_interface::{
        FieldIdx, PlaceTy, RustBitSet,
        index::Idx,
        middle::{
            mir::{
                self, BasicBlock, Body, HasLocalDecls, Local, Mutability, Place as MirPlace,
                PlaceElem, ProjectionElem, VarDebugInfoContents,
            },
            ty::{TyCtxt, TyKind},
        },
    },
    validity_checks_enabled,
};

use crate::rustc_interface::mir_dataflow;

use crate::{
    borrow_pcg::region_projection::PcgRegion,
    error::{PcgError, PcgUnsupportedError},
};

use super::Place;

#[derive(Debug, Clone, Copy)]
pub enum ProjectionKind {
    DerefRef(Mutability),
    DerefRawPtr(Mutability),
    DerefBox,
    Field(FieldIdx),
    ConstantIndex(ConstantIndex),
    Other,
}
// TODO: Merge with ExpandedPlace?
#[derive(Clone)]
pub struct ShallowExpansion<'tcx> {
    pub(crate) target_place: Place<'tcx>,

    /// Other places that could have resulted from this expansion. Note: this
    /// vector is always incomplete when projecting with `Index` or `Subslice`
    /// and also when projecting a slice type with `ConstantIndex`!
    pub(crate) other_places: Vec<Place<'tcx>>,
    pub(crate) kind: ProjectionKind,
}

impl<'tcx> ShallowExpansion<'tcx> {
    pub(crate) fn new<'a>(
        target_place: Place<'tcx>,
        other_places: Vec<Place<'tcx>>,
        kind: ProjectionKind,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Self
    where
        'tcx: 'a,
    {
        if validity_checks_enabled() && matches!(kind, ProjectionKind::DerefRef(_)) {
            pcg_validity_assert!(!target_place.is_owned(ctxt));
        }
        Self {
            target_place,
            other_places,
            kind,
        }
    }

    pub(crate) fn base_place(&self) -> Place<'tcx> {
        self.target_place.last_projection().unwrap().0
    }

    pub(crate) fn guide(&self) -> Option<RepackGuide> {
        self.target_place
            .last_projection()
            .unwrap()
            .1
            .try_into()
            .ok()
    }

    pub fn expansion(&self) -> Vec<Place<'tcx>> {
        let mut expansion = self.other_places.clone();
        self.kind
            .insert_target_into_expansion(self.target_place, &mut expansion);
        expansion
    }

    fn dest_places_for_region<'a>(
        &self,
        region: PcgRegion,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Vec<Place<'tcx>>
    where
        'tcx: 'a,
    {
        self.expansion()
            .iter()
            .filter(|e| {
                e.lifetime_projections(ctxt)
                    .into_iter()
                    .any(|child_rp| region == child_rp.region(ctxt))
            })
            .copied()
            .collect::<Vec<_>>()
    }

    pub(crate) fn place_expansion_for_region<'a>(
        &self,
        region: PcgRegion,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Option<PlaceExpansion<'tcx>>
    where
        'tcx: 'a,
    {
        let dest_places = self.dest_places_for_region(region, ctxt);
        if dest_places.is_empty() {
            None
        } else {
            Some(PlaceExpansion::from_places(dest_places, ctxt))
        }
    }
}

impl ProjectionKind {
    pub(crate) fn is_deref_box(self) -> bool {
        matches!(self, ProjectionKind::DerefBox)
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

pub trait HasCompilerCtxt<'a, 'tcx>: Copy {
    fn ctxt(&self) -> CompilerCtxt<'a, 'tcx, ()>;
    fn body(&self) -> &'a Body<'tcx> {
        self.ctxt().body()
    }
    fn tcx(&self) -> TyCtxt<'tcx>
    where
        'tcx: 'a,
    {
        self.ctxt().tcx()
    }
}

#[derive(Clone, Copy)]
pub(crate) enum ToGraph {
    Phase(DataflowStmtPhase),
    Action(EvalStmtPhase, usize),
}

#[derive(Clone, Serialize, Default, Debug)]
pub(crate) struct StmtGraphs {
    at_phase: Vec<(DataflowStmtPhase, String)>,
    actions: BTreeMap<EvalStmtPhase, Vec<String>>,
}

impl StmtGraphs {
    pub(crate) fn relative_filename(location: mir::Location, to_graph: ToGraph) -> String {
        match to_graph {
            ToGraph::Phase(phase) => {
                format!(
                    "{:?}_stmt_{}_{}.dot",
                    location.block,
                    location.statement_index,
                    phase.to_filename_str_part()
                )
            }
            ToGraph::Action(phase, action_idx) => {
                format!(
                    "{:?}_stmt_{}_{:?}_action_{}.dot",
                    location.block, location.statement_index, phase, action_idx,
                )
            }
        }
    }

    pub(crate) fn insert_for_phase(&mut self, phase: DataflowStmtPhase, filename: String) {
        self.at_phase.push((phase, filename));
    }

    pub(crate) fn insert_for_action(
        &mut self,
        phase: EvalStmtPhase,
        action_idx: usize,
        filename: String,
    ) {
        let within_phase = self.actions.entry(phase).or_default();
        assert_eq!(
            within_phase.len(),
            action_idx,
            "Action index {} isn't equal to number of existing actions for {:?}",
            action_idx,
            phase
        );
        within_phase.push(filename);
    }
}

pub(crate) trait DataflowCtxt<'a, 'tcx: 'a>: HasBorrowCheckerCtxt<'a, 'tcx> {
    fn try_into_analysis_ctxt(self) -> Option<AnalysisCtxt<'a, 'tcx>>;
}
pub trait HasBorrowCheckerCtxt<'a, 'tcx, BC = &'a dyn BorrowCheckerInterface<'tcx>>:
    HasCompilerCtxt<'a, 'tcx>
{
    fn bc(&self) -> BC;
    fn bc_ctxt(&self) -> CompilerCtxt<'a, 'tcx, BC>;
}

impl<'a, 'tcx, T: Copy> HasCompilerCtxt<'a, 'tcx> for CompilerCtxt<'a, 'tcx, T> {
    fn ctxt(&self) -> CompilerCtxt<'a, 'tcx, ()> {
        CompilerCtxt::new(self.mir, self.tcx, ())
    }

    fn body(&self) -> &'a Body<'tcx> {
        self.mir
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
}

impl<'a, 'tcx, T: Copy> HasBorrowCheckerCtxt<'a, 'tcx, T> for CompilerCtxt<'a, 'tcx, T> {
    fn bc(&self) -> T {
        self.bc
    }

    fn bc_ctxt(&self) -> CompilerCtxt<'a, 'tcx, T> {
        *self
    }
}

#[derive(Copy, Clone)]
pub struct CompilerCtxt<'a, 'tcx, T = &'a dyn BorrowCheckerInterface<'tcx>> {
    pub(super) mir: &'a Body<'tcx>,
    pub(super) tcx: TyCtxt<'tcx>,
    pub(crate) bc: T,
}

impl<T: Copy> std::fmt::Debug for CompilerCtxt<'_, '_, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "CompilerCtxt",)
    }
}

impl<'a, 'tcx, T: BorrowCheckerInterface<'tcx> + ?Sized> CompilerCtxt<'a, 'tcx, &'a T> {
    pub fn as_dyn(self) -> CompilerCtxt<'a, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>> {
        CompilerCtxt {
            mir: self.mir,
            tcx: self.tcx(),
            bc: self.bc.as_dyn(),
        }
    }
}

impl<'a, 'tcx, T> CompilerCtxt<'a, 'tcx, T> {
    pub fn new(mir: &'a Body<'tcx>, tcx: TyCtxt<'tcx>, bc: T) -> Self {
        Self { mir, tcx, bc }
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

    pub fn local_place(&self, var_name: &str) -> Option<Place<'tcx>> {
        for info in &self.mir.var_debug_info {
            if let VarDebugInfoContents::Place(place) = info.value
                && info.name.to_string() == var_name
            {
                return Some(place.into());
            }
        }
        None
    }
}

impl CompilerCtxt<'_, '_> {
    /// Returns `true` iff the edge from `from` to `to` is a back edge (i.e.
    /// `to` dominates `from`).
    pub(crate) fn is_back_edge(&self, from: BasicBlock, to: BasicBlock) -> bool {
        self.mir.basic_blocks.dominators().dominates(to, from)
    }

    pub fn num_args(self) -> usize {
        self.mir.arg_count
    }

    pub fn local_count(self) -> usize {
        self.mir.local_decls().len()
    }

    pub fn always_live_locals(self) -> RustBitSet<Local> {
        mir_dataflow::impls::always_storage_live_locals(self.mir)
    }

    pub fn always_live_locals_non_args(self) -> RustBitSet<Local> {
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

impl From<ConstantIndex> for PlaceElem<'_> {
    fn from(val: ConstantIndex) -> Self {
        PlaceElem::ConstantIndex {
            offset: val.offset,
            min_length: val.min_length,
            from_end: val.from_end,
        }
    }
}

impl ConstantIndex {
    pub(crate) fn other_places<'a, 'tcx>(
        self,
        from: Place<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Vec<Place<'tcx>>
    where
        'tcx: 'a,
    {
        self.other_elems()
            .into_iter()
            .map(|e| from.project_deeper(e, ctxt).unwrap())
            .collect()
    }

    pub(crate) fn other_elems<'tcx>(self) -> Vec<PlaceElem<'tcx>> {
        let range = if self.from_end {
            1..self.min_length + 1
        } else {
            0..self.min_length
        };
        assert!(range.contains(&self.offset));
        range
            .filter(|&i| i != self.offset)
            .map(|i| ProjectionElem::ConstantIndex {
                offset: i,
                min_length: self.min_length,
                from_end: self.from_end,
            })
            .collect()
    }
}

impl<'tcx> Place<'tcx> {
    pub fn to_rust_place<'a>(self, ctxt: impl HasCompilerCtxt<'a, 'tcx>) -> MirPlace<'tcx>
    where
        'tcx: 'a,
    {
        MirPlace {
            local: self.local,
            projection: ctxt.tcx().mk_place_elems(self.projection),
        }
    }

    /// Expand `self` one level down by following the `guide_place`.
    /// Returns the new `self` and a vector containing other places that
    /// could have resulted from the expansion.
    pub fn expand_one_level<'a>(
        self,
        guide_place: Self,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Result<ShallowExpansion<'tcx>, PcgError>
    where
        'tcx: 'a,
    {
        let index = self.projection.len();
        assert!(
            index < guide_place.projection.len(),
            "self place {self:?} is not a prefix of guide place {guide_place:?}"
        );
        let new_projection = ctxt.tcx().mk_place_elems_from_iter(
            self.projection
                .iter()
                .copied()
                .chain([guide_place.projection[index]]),
        );
        let new_current_place = Place::new(self.local, new_projection);
        let (other_places, kind) = match guide_place.projection[index] {
            ProjectionElem::Field(projected_field, _field_ty) => {
                let other_places = self.expand_field(Some(projected_field.index()), ctxt)?;
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
                let other_places = ConstantIndex {
                    offset,
                    min_length,
                    from_end,
                }
                .other_places(self, ctxt);
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
                let typ = self.ty(ctxt);
                let kind = match typ.ty.kind() {
                    TyKind::Ref(_, _, mutbl) => ProjectionKind::DerefRef(*mutbl),
                    TyKind::RawPtr(_, mutbl) => ProjectionKind::DerefRawPtr(*mutbl),
                    _ if typ.ty.is_box() => ProjectionKind::DerefBox,
                    _ => unreachable!(),
                };
                (Vec::new(), kind)
            }
            ProjectionElem::Index(..)
            | ProjectionElem::Subslice { .. }
            | ProjectionElem::Downcast(..)
            | ProjectionElem::OpaqueCast(..) => (Vec::new(), ProjectionKind::Other),
            _ => todo!(),
        };
        for p in other_places.iter() {
            assert!(
                p.projection.len() == self.projection.len() + 1,
                "expanded place {p:?} is not a direct child of {self:?}",
            );
        }
        Ok(ShallowExpansion::new(
            new_current_place,
            other_places,
            kind,
            ctxt,
        ))
    }

    /// Expands a place `x.f.g` of type struct into a vector of places for
    /// each of the struct's fields `{x.f.g.f, x.f.g.g, x.f.g.h}`. If
    /// `without_field` is not `None`, then omits that field from the final
    /// vector.
    pub fn expand_field<'a>(
        self,
        without_field: Option<usize>,
        repacker: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Result<Vec<Self>, PcgError>
    where
        'tcx: 'a,
    {
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
                        let field_place = repacker.tcx().mk_place_field(
                            self.to_rust_place(repacker),
                            field,
                            field_def.ty(repacker.tcx(), substs),
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
                                .tcx()
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
                        let field_place = repacker.tcx().mk_place_field(
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
                        .tcx()
                        .mk_place_deref(self.to_rust_place(repacker))
                        .into(),
                );
            }
            TyKind::Alias(..) => {
                return Err(PcgError::unsupported(
                    PcgUnsupportedError::ExpansionOfAliasType,
                ));
            }
            _ => unreachable!("ty={:?} ({self:?})", typ),
        }
        Ok(places)
    }
}

impl<'tcx> Place<'tcx> {
    pub fn ty<'a>(self, ctxt: impl HasCompilerCtxt<'a, 'tcx>) -> PlaceTy<'tcx>
    where
        'tcx: 'a,
    {
        debug_assert!(
            ctxt.body().local_decls().len() > self.local.as_usize(),
            "Place {:?} has local {:?}, but the provided MIR at {:?} only has {} local declarations",
            self,
            self.local,
            ctxt.body().span,
            ctxt.body().local_decls().len()
        );
        (*self).ty(ctxt.body(), ctxt.tcx())
    }

    #[allow(unused)]
    pub(crate) fn get_ref_region(&self, repacker: CompilerCtxt<'_, 'tcx>) -> Option<PcgRegion> {
        match self.ty(repacker).ty.kind() {
            TyKind::Ref(region, ..) => Some((*region).into()),
            _ => None,
        }
    }

    pub(crate) fn projects_shared_ref<'a>(self, ctxt: impl HasCompilerCtxt<'a, 'tcx>) -> bool
    where
        'tcx: 'a,
    {
        self.projects_ty(
            |typ| {
                typ.ty
                    .ref_mutability()
                    .map(|m| m.is_not())
                    .unwrap_or_default()
            },
            ctxt,
        )
        .is_some()
    }

    pub(crate) fn projects_ty<'a>(
        self,
        mut predicate: impl FnMut(PlaceTy<'tcx>) -> bool,
        repacker: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Option<Place<'tcx>>
    where
        'tcx: 'a,
    {
        self.projection_tys(repacker.ctxt())
            .find(|(typ, _)| predicate(*typ))
            .map(|(_, proj)| {
                let projection = repacker.tcx().mk_place_elems(proj);
                Self::new(self.local, projection)
            })
    }

    pub(crate) fn projection_tys<'a>(
        self,
        repacker: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> impl Iterator<Item = (PlaceTy<'tcx>, &'tcx [PlaceElem<'tcx>])>
    where
        'tcx: 'a,
    {
        let mut typ = PlaceTy::from_ty(repacker.body().local_decls()[self.local].ty);
        self.projection.iter().enumerate().map(move |(idx, elem)| {
            let ret = (typ, &self.projection[0..idx]);
            typ = typ.projection_ty(repacker.tcx(), *elem);
            ret
        })
    }
}
