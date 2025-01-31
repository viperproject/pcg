use serde_json::json;

use crate::rustc_interface::{ast::Mutability, data_structures::fx::FxHashSet};
use crate::utils::display::DisplayWithRepacker;
use crate::utils::PlaceRepacker;

use super::borrow_pcg_edge::{LocalNode, PCGNode};
use super::coupling_graph_constructor::Coupled;
use super::domain::ToJsonWithRepacker;
use super::edge_data::EdgeData;
use super::{
    domain::MaybeOldPlace, has_pcs_elem::HasPcsElems, region_projection::RegionProjection,
};

/// A PCG hyperedge where at the nodes of at least one of the edge endpoints are
/// all region projections.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct RegionProjectionMember<'tcx> {
    pub(crate) inputs: Coupled<PCGNode<'tcx>>,
    pub(crate) outputs: Coupled<LocalNode<'tcx>>,
    pub(crate) kind: RegionProjectionMemberKind,
}

impl<'tcx> DisplayWithRepacker<'tcx> for RegionProjectionMember<'tcx> {
    fn to_short_string(&self, repacker: PlaceRepacker<'_, 'tcx>) -> String {
        format!(
            "{} -> {}",
            self.inputs.to_short_string(repacker),
            self.outputs.to_short_string(repacker)
        )
    }
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub enum RegionProjectionMemberKind {
    Aggregate {
        field_idx: usize,
        target_rp_index: usize,
    },
    /// Region projections resulting from a new borrow
    BorrowRegionProjections,
    /// TODO: Provide more useful kinds, this enum variant should be removed
    Todo,
}

impl<'tcx> ToJsonWithRepacker<'tcx> for RegionProjectionMember<'tcx> {
    fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        json!({
            "inputs": self.inputs.iter().map(|p| p.to_json(repacker)).collect::<Vec<_>>(),
            "outputs": self.outputs.iter().map(|p| p.to_json(repacker)).collect::<Vec<_>>(),
        })
    }
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

    pub(crate) fn new(
        inputs: Coupled<PCGNode<'tcx>>,
        outputs: Coupled<LocalNode<'tcx>>,
        kind: RegionProjectionMemberKind,
    ) -> Self {
        Self {
            inputs,
            outputs,
            kind,
        }
    }

    pub fn inputs(&self) -> &Coupled<PCGNode<'tcx>> {
        &self.inputs
    }

    pub fn outputs(&self) -> &Coupled<LocalNode<'tcx>> {
        &self.outputs
    }
}
