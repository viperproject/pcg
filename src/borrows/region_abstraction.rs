use rustc_interface::{data_structures::fx::FxHashSet, middle::mir::Location};

use crate::{combined_pcs::{LocalNodeLike, PCGNode}, rustc_interface, utils::{display::DisplayWithRepacker, validity::HasValidityCheck, PlaceRepacker}};

use super::{
    borrow_pcg_edge::LocalNode, domain::{
        AbstractionBlockEdge, AbstractionInputTarget, AbstractionOutputTarget, AbstractionType,
    }, edge_data::EdgeData, has_pcs_elem::HasPcsElems
};

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct AbstractionEdge<'tcx> {
    pub abstraction_type: AbstractionType<'tcx>,
}

impl<'tcx> HasValidityCheck<'tcx> for AbstractionEdge<'tcx> {
    fn check_validity(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Result<(), String> {
        self.abstraction_type.check_validity(repacker)
    }
}

impl<'tcx> DisplayWithRepacker<'tcx> for AbstractionEdge<'tcx> {
    fn to_short_string(&self, repacker: PlaceRepacker<'_, 'tcx>) -> String {
        match &self.abstraction_type {
            AbstractionType::FunctionCall(c) => c.to_short_string(repacker),
            AbstractionType::Loop(c) => c.to_short_string(repacker),
        }
    }
}

impl<'tcx, T> HasPcsElems<T> for AbstractionEdge<'tcx>
where
    AbstractionType<'tcx>: HasPcsElems<T>,
{
    fn pcs_elems(&mut self) -> Vec<&mut T> {
        self.abstraction_type.pcs_elems()
    }
}

impl<'tcx> EdgeData<'tcx> for AbstractionEdge<'tcx> {
    fn blocked_nodes(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<PCGNode<'tcx>> {
        self.inputs().into_iter().map(|i| i.into()).collect()
    }

    fn blocked_by_nodes(
        &self,
        _repacker: PlaceRepacker<'_, 'tcx>,
    ) -> FxHashSet<LocalNode<'tcx>> {
        self.outputs().into_iter().map(|o| o.to_local_node()).collect()
    }

    fn is_owned_expansion(&self) -> bool {
        false
    }
}

impl<'tcx> AbstractionEdge<'tcx> {
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

    pub fn edges(&self) -> Vec<AbstractionBlockEdge<'tcx>> {
        self.abstraction_type.edges()
    }
}
