use crate::rustc_interface::{ast::Mutability, data_structures::fx::FxHashSet};
use crate::utils::PlaceRepacker;

use super::borrow_pcg_edge::{LocalNode, PCGNode};
use super::coupling_graph_constructor::Coupled;
use super::edge_data::EdgeData;
use super::{
    domain::{MaybeOldPlace, MaybeRemotePlace},
    has_pcs_elem::HasPcsElems,
    region_projection::RegionProjection,
};
#[derive(Clone, Debug, Hash, PartialEq, Eq, Copy)]
pub enum RegionProjectionMemberDirection {
    ProjectionBlocksPlace,
    PlaceBlocksProjection,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct RegionProjectionMember<'tcx> {
    pub(crate) inputs: Coupled<PCGNode<'tcx>>,
    pub(crate) outputs: Coupled<LocalNode<'tcx>>,
}

impl<'tcx> EdgeData<'tcx> for RegionProjectionMember<'tcx> {
    fn blocked_by_nodes(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<LocalNode<'tcx>> {
        self.outputs.iter().cloned().collect()
    }

    fn blocked_nodes(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<PCGNode<'tcx>> {
        self.inputs.iter().cloned().collect()
    }

    fn is_owned_expansion(&self) -> bool {
        false
    }
}

impl<'tcx> HasPcsElems<RegionProjection<'tcx>> for RegionProjectionMember<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut RegionProjection<'tcx>> {
        self.inputs.iter_mut().flat_map(|p| p.pcs_elems()).collect()
    }
}
impl<'tcx> HasPcsElems<RegionProjection<'tcx, MaybeOldPlace<'tcx>>>
    for RegionProjectionMember<'tcx>
{
    fn pcs_elems(&mut self) -> Vec<&mut RegionProjection<'tcx, MaybeOldPlace<'tcx>>> {
        self.outputs
            .iter_mut()
            .flat_map(|p| p.pcs_elems())
            .collect()
    }
}

impl<'tcx> HasPcsElems<MaybeOldPlace<'tcx>> for RegionProjectionMember<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        self.inputs
            .iter_mut()
            .flat_map(|p| p.pcs_elems())
            .chain(self.outputs.iter_mut().flat_map(|p| p.pcs_elems()))
            .collect()
    }
}

impl<'tcx> RegionProjectionMember<'tcx> {
    /// Returns `true` iff the lifetime projections are mutable
    pub(crate) fn mutability(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Mutability {
        self.inputs.mutability(repacker)
    }

    pub(crate) fn new(inputs: Coupled<PCGNode<'tcx>>, outputs: Coupled<LocalNode<'tcx>>) -> Self {
        Self { inputs, outputs }
    }

    pub fn inputs(&self) -> &Coupled<PCGNode<'tcx>> {
        &self.inputs
    }

    pub fn outputs(&self) -> &Coupled<LocalNode<'tcx>> {
        &self.outputs
    }
}
