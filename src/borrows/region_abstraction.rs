use rustc_interface::{data_structures::fx::FxHashSet, middle::mir::Location};

use crate::rustc_interface;

use super::{
    borrow_pcg_edge::BlockedNode,
    domain::{
        AbstractionBlockEdge, AbstractionInputTarget, AbstractionOutputTarget, AbstractionType,
        MaybeOldPlace,
    },
    has_pcs_elem::HasPcsElems,
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
    pub fn new(abstraction_type: AbstractionType<'tcx>) -> Self {
        Self { abstraction_type }
    }

    pub fn location(&self) -> Location {
        self.abstraction_type.location()
    }

    pub fn blocked_nodes(&self) -> FxHashSet<BlockedNode<'tcx>> {
        self.inputs().into_iter().map(|i| i.into()).collect()
    }

    pub fn inputs(&self) -> Vec<AbstractionInputTarget<'tcx>> {
        self.abstraction_type.inputs()
    }

    pub fn outputs(&self) -> Vec<AbstractionOutputTarget<'tcx>> {
        self.abstraction_type.outputs()
    }

    pub fn edges(&self) -> Vec<AbstractionBlockEdge<'tcx>> {
        self.abstraction_type.edges()
    }
}
