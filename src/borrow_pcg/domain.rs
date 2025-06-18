use super::region_projection::RegionProjection;
use crate::{
    borrow_pcg::{
        edge_data::LabelPlacePredicate,
        has_pcs_elem::{HasPcgElems, LabelPlace},
        latest::Latest,
    },
    pcg::PCGNode,
    utils::{maybe_remote::MaybeRemotePlace, place::maybe_old::MaybeOldPlace, CompilerCtxt},
};

pub type FunctionCallAbstractionInput<'tcx> = RegionProjection<'tcx, MaybeOldPlace<'tcx>>;

impl<'tcx> LabelPlace<'tcx> for FunctionCallAbstractionInput<'tcx> {
    fn label_place(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        latest: &Latest<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        let mut changed = false;
        for p in self.pcg_elems() {
            changed |= p.label_place(predicate, latest, ctxt);
        }
        changed
    }
}

pub type LoopAbstractionInput<'tcx> = PCGNode<'tcx, MaybeRemotePlace<'tcx>, MaybeRemotePlace<'tcx>>;

impl<'tcx> LabelPlace<'tcx> for LoopAbstractionInput<'tcx> {
    fn label_place(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        latest: &Latest<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        let mut changed = false;
        for p in self.pcg_elems() {
            changed |= p.label_place(predicate, latest, ctxt);
        }
        changed
    }
}

impl<'tcx> From<RegionProjection<'tcx, MaybeOldPlace<'tcx>>> for LoopAbstractionInput<'tcx> {
    fn from(value: RegionProjection<'tcx, MaybeOldPlace<'tcx>>) -> Self {
        PCGNode::RegionProjection(value.into())
    }
}

impl<'tcx> TryFrom<LoopAbstractionInput<'tcx>> for RegionProjection<'tcx> {
    type Error = ();

    fn try_from(value: LoopAbstractionInput<'tcx>) -> Result<Self, Self::Error> {
        match value {
            PCGNode::RegionProjection(rp) => Ok(rp.into()),
            _ => Err(()),
        }
    }
}

pub type AbstractionInputTarget<'tcx> =
    PCGNode<'tcx, MaybeRemotePlace<'tcx>, MaybeRemotePlace<'tcx>>;
pub type AbstractionOutputTarget<'tcx> = RegionProjection<'tcx, MaybeOldPlace<'tcx>>;
