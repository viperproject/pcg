use derive_more::{Deref, DerefMut, From};

use super::region_projection::RegionProjection;
use crate::{
    borrow_checker::BorrowCheckerInterface,
    borrow_pcg::{
        borrow_pcg_edge::LocalNode,
        edge_data::{LabelPlaceCtxt, LabelPlacePredicate},
        has_pcs_elem::{
            HasPcgElems, LabelPlace, LabelPlaceWithCtxt, LabelRegionProjection,
            LabelRegionProjectionPredicate, LabelRegionProjectionResult, PlaceLabeller,
        },
        region_projection::RegionProjectionLabel,
    },
    pcg::{PCGNode, PCGNodeLike},
    utils::{
        CompilerCtxt, Place, display::DisplayWithCompilerCtxt, maybe_remote::MaybeRemotePlace,
        place::maybe_old::MaybeOldPlace, validity::HasValidityCheck,
    },
};

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash, From, Deref, DerefMut)]
pub struct FunctionCallAbstractionInput<'tcx>(
    pub(crate) RegionProjection<'tcx, MaybeOldPlace<'tcx>>,
);

impl<'tcx> LabelRegionProjection<'tcx> for FunctionCallAbstractionInput<'tcx> {
    fn label_region_projection(
        &mut self,
        predicate: &LabelRegionProjectionPredicate<'tcx>,
        label: Option<RegionProjectionLabel>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> LabelRegionProjectionResult {
        self.0.label_region_projection(predicate, label, ctxt)
    }
}

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

impl<'tcx> DisplayWithCompilerCtxt<'tcx, &dyn BorrowCheckerInterface<'tcx>>
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
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        let mut changed = false;
        for p in self.pcg_elems() {
            changed |= p.label_place_with_ctxt(
                predicate,
                LabelPlaceCtxt::RegionProjection,
                labeller,
                ctxt,
            );
        }
        changed
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash, From, Deref)]
pub(crate) struct LoopAbstractionInput<'tcx>(pub(crate) PCGNode<'tcx>);

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash, From, Deref)]
pub(crate) struct LoopAbstractionOutput<'tcx>(pub(crate) LocalNode<'tcx>);

impl<'tcx> From<MaybeRemotePlace<'tcx>> for LoopAbstractionInput<'tcx> {
    fn from(value: MaybeRemotePlace<'tcx>) -> Self {
        LoopAbstractionInput(value.into())
    }
}

impl<'tcx> LabelRegionProjection<'tcx> for LoopAbstractionInput<'tcx> {
    fn label_region_projection(
        &mut self,
        projection: &LabelRegionProjectionPredicate<'tcx>,
        label: Option<RegionProjectionLabel>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> LabelRegionProjectionResult {
        self.0.label_region_projection(projection, label, ctxt)
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
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        let mut changed = false;
        let label_ctxt = LabelPlaceCtxt::for_pcg_node(self.0);
        for p in self.pcg_elems() {
            changed |= p.label_place_with_ctxt(
                predicate,
                label_ctxt,
                labeller,
                ctxt,
            );
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
            PCGNode::RegionProjection(rp) => Ok(rp),
            _ => Err(()),
        }
    }
}

impl<'tcx> LabelRegionProjection<'tcx> for LoopAbstractionOutput<'tcx> {
    fn label_region_projection(
        &mut self,
        projection: &LabelRegionProjectionPredicate<'tcx>,
        label: Option<RegionProjectionLabel>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> LabelRegionProjectionResult {
        self.0.label_region_projection(projection, label, ctxt)
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
    fn to_pcg_node<C: Copy>(self, _ctxt: CompilerCtxt<'_, 'tcx, C>) -> PCGNode<'tcx> {
        self.0.into()
    }
}

impl<'tcx> HasValidityCheck<'tcx> for LoopAbstractionOutput<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        self.0.check_validity(ctxt)
    }
}

impl<'tcx> LabelPlace<'tcx> for LoopAbstractionOutput<'tcx> {
    fn label_place(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        let mut changed = false;
        let label_ctxt = LabelPlaceCtxt::for_pcg_node(self.0);
        let maybe_old_places: Vec<&mut MaybeOldPlace<'tcx>> = self.0.pcg_elems();
        for p in maybe_old_places {
            changed |= p.label_place_with_ctxt(
                predicate,
                label_ctxt,
                labeller,
                ctxt,
            );
        }
        changed
    }
}

impl<'tcx> From<RegionProjection<'tcx, MaybeOldPlace<'tcx>>> for LoopAbstractionOutput<'tcx> {
    fn from(value: RegionProjection<'tcx, MaybeOldPlace<'tcx>>) -> Self {
        LoopAbstractionOutput(PCGNode::RegionProjection(value))
    }
}

impl<'tcx> TryFrom<LoopAbstractionOutput<'tcx>> for RegionProjection<'tcx> {
    type Error = ();

    fn try_from(value: LoopAbstractionOutput<'tcx>) -> Result<Self, Self::Error> {
        match value.0 {
            PCGNode::RegionProjection(rp) => Ok(rp.into()),
            _ => Err(()),
        }
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash, From, Deref)]
pub struct AbstractionInputTarget<'tcx>(pub(crate) PCGNode<'tcx>);

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash, From, Deref)]
pub struct AbstractionOutputTarget<'tcx>(pub(crate) LocalNode<'tcx>);

impl<'tcx> LabelPlace<'tcx> for AbstractionOutputTarget<'tcx> {
    fn label_place(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.0.label_place(predicate, labeller, ctxt)
    }
}

impl<'tcx> LabelRegionProjection<'tcx> for AbstractionOutputTarget<'tcx> {
    fn label_region_projection(
        &mut self,
        projection: &LabelRegionProjectionPredicate<'tcx>,
        label: Option<RegionProjectionLabel>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> LabelRegionProjectionResult {
        self.0.label_region_projection(projection, label, ctxt)
    }
}

impl<'tcx> HasValidityCheck<'tcx> for AbstractionOutputTarget<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        self.0.check_validity(ctxt)
    }
}

impl<'tcx> HasPcgElems<MaybeOldPlace<'tcx>> for AbstractionOutputTarget<'tcx> {
    fn pcg_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        self.0.pcg_elems()
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

impl<'tcx> From<RegionProjection<'tcx, Place<'tcx>>> for FunctionCallAbstractionOutput<'tcx> {
    fn from(value: RegionProjection<'tcx, Place<'tcx>>) -> Self {
        FunctionCallAbstractionInput(value.into())
    }
}
