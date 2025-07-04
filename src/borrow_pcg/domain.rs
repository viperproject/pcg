use derive_more::{Deref, DerefMut, From};

use super::region_projection::RegionProjection;
use crate::{
    borrow_checker::BorrowCheckerInterface,
    borrow_pcg::{
        borrow_pcg_edge::LocalNode,
        edge_data::LabelPlacePredicate,
        has_pcs_elem::{HasPcgElems, LabelPlace},
        latest::Latest,
    },
    pcg::{PCGNode, PCGNodeLike},
    utils::{
        display::DisplayWithCompilerCtxt, maybe_remote::MaybeRemotePlace,
        place::maybe_old::MaybeOldPlace, validity::HasValidityCheck, CompilerCtxt,
    },
};

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash, From, Deref, DerefMut)]
pub(crate) struct FunctionCallAbstractionInput<'tcx>(
    pub(crate) RegionProjection<'tcx, MaybeOldPlace<'tcx>>,
);

impl<'tcx> PCGNodeLike<'tcx> for FunctionCallAbstractionInput<'tcx> {
    fn to_pcg_node<C: Copy>(self, _ctxt: CompilerCtxt<'_, 'tcx, C>) -> PCGNode<'tcx> {
        self.0.into()
    }
}

impl<'tcx> HasValidityCheck<'tcx> for FunctionCallAbstractionInput<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        self.0.check_validity(ctxt)
    }
}

impl<'a, 'tcx> DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>
    for FunctionCallAbstractionInput<'tcx>
{
    fn to_short_string(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> String {
        self.0.to_short_string(ctxt)
    }
}

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

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash, From, Deref)]
pub(crate) struct LoopAbstractionInput<'tcx>(pub(crate) PCGNode<'tcx>);

impl<'tcx> From<MaybeRemotePlace<'tcx>> for LoopAbstractionInput<'tcx> {
    fn from(value: MaybeRemotePlace<'tcx>) -> Self {
        LoopAbstractionInput(value.into())
    }
}

impl<'a, 'tcx> DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>
    for LoopAbstractionInput<'tcx>
{
    fn to_short_string(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> String {
        self.0.to_short_string(ctxt)
    }
}

impl<'tcx> PCGNodeLike<'tcx> for LoopAbstractionInput<'tcx> {
    fn to_pcg_node<C: Copy>(self, _ctxt: CompilerCtxt<'_, 'tcx, C>) -> PCGNode<'tcx> {
        self.0
    }
}

impl<'tcx> HasValidityCheck<'tcx> for LoopAbstractionInput<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        self.0.check_validity(ctxt)
    }
}

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
        LoopAbstractionInput(PCGNode::RegionProjection(value.into()))
    }
}

impl<'tcx> TryFrom<LoopAbstractionInput<'tcx>> for RegionProjection<'tcx> {
    type Error = ();

    fn try_from(value: LoopAbstractionInput<'tcx>) -> Result<Self, Self::Error> {
        match value.0 {
            PCGNode::RegionProjection(rp) => Ok(rp.into()),
            _ => Err(()),
        }
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash, From, Deref)]
pub(crate) struct AbstractionInputTarget<'tcx>(pub(crate) PCGNode<'tcx>);

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash, From, Deref)]
pub(crate) struct AbstractionOutputTarget<'tcx>(pub(crate) LocalNode<'tcx>);
