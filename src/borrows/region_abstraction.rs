use rustc_interface::{data_structures::fx::FxHashSet, middle::mir::Location};

use crate::{rustc_interface, utils::Place};

use super::{
    domain::{
        AbstractionBlockEdge, AbstractionInputTarget, AbstractionOutputTarget,
        AbstractionType, MaybeOldPlace, MaybeRemotePlace,
    }, has_pcs_elem::HasPcsElems, latest::Latest
};

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct AbstractionEdge<'tcx> {
    pub abstraction_type: AbstractionType<'tcx>,
}

impl<'tcx> HasPcsElems<MaybeOldPlace<'tcx>> for AbstractionEdge<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        self.abstraction_type.pcs_elems()
    }
}

impl<'tcx> AbstractionEdge<'tcx> {
    pub fn make_place_old(&mut self, place: Place<'tcx>, latest: &Latest) {
        self.abstraction_type.make_place_old(place, latest);
    }

    pub fn new(abstraction_type: AbstractionType<'tcx>) -> Self {
        Self { abstraction_type }
    }

    pub fn location(&self) -> Location {
        self.abstraction_type.location()
    }

    pub fn inputs(&self) -> Vec<AbstractionInputTarget<'tcx>> {
        self.abstraction_type.inputs()
    }

    pub fn outputs(&self) -> Vec<AbstractionOutputTarget<'tcx>> {
        self.abstraction_type.outputs()
    }

    pub fn blocks(&self, place: MaybeRemotePlace<'tcx>) -> bool {
        self.abstraction_type.blocks(place)
    }

    pub fn blocks_places(&self) -> FxHashSet<MaybeRemotePlace<'tcx>> {
        self.abstraction_type.blocks_places()
    }

    pub fn blocked_by_places(&self) -> FxHashSet<MaybeOldPlace<'tcx>> {
        self.abstraction_type.blocker_places()
    }

    pub fn edges(&self) -> Vec<AbstractionBlockEdge<'tcx>> {
        self.abstraction_type.edges()
    }
}
