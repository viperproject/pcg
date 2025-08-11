use derive_more::{Deref, DerefMut, From};

use super::region_projection::LifetimeProjection;
use crate::{
    borrow_checker::BorrowCheckerInterface,
    borrow_pcg::{
        borrow_pcg_edge::LocalNode,
        edge_data::LabelPlacePredicate,
        has_pcs_elem::{
            LabelLifetimeProjection, LabelLifetimeProjectionPredicate,
            LabelLifetimeProjectionResult, LabelNodeContext, LabelPlace, LabelPlaceWithContext,
            PlaceLabeller,
        },
        region_projection::{LifetimeProjectionLabel, LocalLifetimeProjection},
    },
    pcg::{PCGNodeLike, PcgNode},
    utils::{
        CompilerCtxt, Place, display::DisplayWithCompilerCtxt, maybe_remote::MaybeRemotePlace,
        place::maybe_old::MaybeLabelledPlace, validity::HasValidityCheck,
    },
};

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash, From, Deref, DerefMut)]
pub struct FunctionCallAbstractionInput<'tcx>(pub(crate) LocalLifetimeProjection<'tcx>);

impl<'tcx> LabelLifetimeProjection<'tcx> for FunctionCallAbstractionInput<'tcx> {
    fn label_lifetime_projection(
        &mut self,
        predicate: &LabelLifetimeProjectionPredicate<'tcx>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> LabelLifetimeProjectionResult {
        self.0.label_lifetime_projection(predicate, label, ctxt)
    }
}

impl<'tcx> PCGNodeLike<'tcx> for FunctionCallAbstractionInput<'tcx> {
    fn to_pcg_node<C: Copy>(self, _ctxt: CompilerCtxt<'_, 'tcx, C>) -> PcgNode<'tcx> {
        self.0.into()
    }
}

impl<'tcx> HasValidityCheck<'tcx> for FunctionCallAbstractionInput<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        self.0.check_validity(ctxt)
    }
}

impl<'tcx> DisplayWithCompilerCtxt<'tcx, &dyn BorrowCheckerInterface<'tcx>>
    for FunctionCallAbstractionInput<'tcx>
{
    fn to_short_string(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> String {
        self.0.to_short_string(ctxt)
    }
}

impl<'tcx> LabelPlaceWithContext<'tcx, LabelNodeContext> for FunctionCallAbstractionInput<'tcx> {
    fn label_place_with_context(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        label_context: LabelNodeContext,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.0
            .label_place_with_context(predicate, labeller, label_context, ctxt)
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash, From, Deref)]
pub(crate) struct LoopAbstractionInput<'tcx>(pub(crate) PcgNode<'tcx>);

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash, From, Deref)]
pub(crate) struct LoopAbstractionOutput<'tcx>(pub(crate) LocalNode<'tcx>);

impl<'tcx> From<MaybeRemotePlace<'tcx>> for LoopAbstractionInput<'tcx> {
    fn from(value: MaybeRemotePlace<'tcx>) -> Self {
        LoopAbstractionInput(value.into())
    }
}

impl<'tcx> LabelLifetimeProjection<'tcx> for LoopAbstractionInput<'tcx> {
    fn label_lifetime_projection(
        &mut self,
        projection: &LabelLifetimeProjectionPredicate<'tcx>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> LabelLifetimeProjectionResult {
        self.0.label_lifetime_projection(projection, label, ctxt)
    }
}

impl<'tcx> DisplayWithCompilerCtxt<'tcx, &dyn BorrowCheckerInterface<'tcx>>
    for LoopAbstractionInput<'tcx>
{
    fn to_short_string(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> String {
        self.0.to_short_string(ctxt)
    }
}

impl<'tcx> PCGNodeLike<'tcx> for LoopAbstractionInput<'tcx> {
    fn to_pcg_node<C: Copy>(self, _ctxt: CompilerCtxt<'_, 'tcx, C>) -> PcgNode<'tcx> {
        self.0
    }
}

impl<'tcx> HasValidityCheck<'tcx> for LoopAbstractionInput<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        self.0.check_validity(ctxt)
    }
}

impl<'tcx> LabelPlaceWithContext<'tcx, LabelNodeContext> for LoopAbstractionInput<'tcx> {
    fn label_place_with_context(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        label_context: LabelNodeContext,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.0
            .label_place_with_context(predicate, labeller, label_context, ctxt)
    }
}

impl<'tcx> From<LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>>> for LoopAbstractionInput<'tcx> {
    fn from(value: LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>>) -> Self {
        LoopAbstractionInput(PcgNode::LifetimeProjection(value.into()))
    }
}

impl<'tcx> TryFrom<LoopAbstractionInput<'tcx>> for LifetimeProjection<'tcx> {
    type Error = ();

    fn try_from(value: LoopAbstractionInput<'tcx>) -> Result<Self, Self::Error> {
        match value.0 {
            PcgNode::LifetimeProjection(rp) => Ok(rp),
            _ => Err(()),
        }
    }
}

impl<'tcx> LabelLifetimeProjection<'tcx> for LoopAbstractionOutput<'tcx> {
    fn label_lifetime_projection(
        &mut self,
        projection: &LabelLifetimeProjectionPredicate<'tcx>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> LabelLifetimeProjectionResult {
        self.0.label_lifetime_projection(projection, label, ctxt)
    }
}

impl<'tcx> DisplayWithCompilerCtxt<'tcx, &dyn BorrowCheckerInterface<'tcx>>
    for LoopAbstractionOutput<'tcx>
{
    fn to_short_string(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> String {
        self.0.to_short_string(ctxt)
    }
}

impl<'tcx> PCGNodeLike<'tcx> for LoopAbstractionOutput<'tcx> {
    fn to_pcg_node<C: Copy>(self, _ctxt: CompilerCtxt<'_, 'tcx, C>) -> PcgNode<'tcx> {
        self.0.into()
    }
}

impl<'tcx> HasValidityCheck<'tcx> for LoopAbstractionOutput<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        self.0.check_validity(ctxt)
    }
}

impl<'tcx> LabelPlaceWithContext<'tcx, LabelNodeContext> for LoopAbstractionOutput<'tcx> {
    fn label_place_with_context(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        label_context: LabelNodeContext,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.0
            .label_place_with_context(predicate, labeller, label_context, ctxt)
    }
}

impl<'tcx> From<LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>>>
    for LoopAbstractionOutput<'tcx>
{
    fn from(value: LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>>) -> Self {
        LoopAbstractionOutput(PcgNode::LifetimeProjection(value))
    }
}

impl<'tcx> TryFrom<LoopAbstractionOutput<'tcx>> for LifetimeProjection<'tcx> {
    type Error = ();

    fn try_from(value: LoopAbstractionOutput<'tcx>) -> Result<Self, Self::Error> {
        match value.0 {
            PcgNode::LifetimeProjection(rp) => Ok(rp.into()),
            _ => Err(()),
        }
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash, From, Deref)]
pub struct AbstractionInputTarget<'tcx>(pub(crate) PcgNode<'tcx>);

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash, From, Deref)]
pub struct AbstractionOutputTarget<'tcx>(pub(crate) LocalNode<'tcx>);

impl<'tcx> LabelPlace<'tcx> for AbstractionOutputTarget<'tcx> {
    fn label_place(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.0
            .label_place_with_context(predicate, labeller, LabelNodeContext::Other, ctxt)
    }
}

impl<'tcx> LabelLifetimeProjection<'tcx> for AbstractionOutputTarget<'tcx> {
    fn label_lifetime_projection(
        &mut self,
        projection: &LabelLifetimeProjectionPredicate<'tcx>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> LabelLifetimeProjectionResult {
        self.0.label_lifetime_projection(projection, label, ctxt)
    }
}

impl<'tcx> HasValidityCheck<'tcx> for AbstractionOutputTarget<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        self.0.check_validity(ctxt)
    }
}

impl<'tcx> DisplayWithCompilerCtxt<'tcx, &dyn BorrowCheckerInterface<'tcx>>
    for AbstractionOutputTarget<'tcx>
{
    fn to_short_string(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> String {
        self.0.to_short_string(ctxt)
    }
}

pub type FunctionCallAbstractionOutput<'tcx> = FunctionCallAbstractionInput<'tcx>;

impl<'tcx> From<LifetimeProjection<'tcx, Place<'tcx>>> for FunctionCallAbstractionOutput<'tcx> {
    fn from(value: LifetimeProjection<'tcx, Place<'tcx>>) -> Self {
        FunctionCallAbstractionInput(value.into())
    }
}
