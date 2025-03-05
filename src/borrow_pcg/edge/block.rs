use serde_json::json;
use smallvec::SmallVec;

use crate::combined_pcs::PCGNode;
use crate::rustc_interface::data_structures::fx::FxHashSet;
use crate::utils::display::DisplayWithRepacker;
use crate::utils::place::maybe_old::MaybeOldPlace;
use crate::utils::validity::HasValidityCheck;
use crate::utils::PlaceRepacker;

use crate::borrow_pcg::borrow_pcg_edge::{BlockedNode, LocalNode};
use crate::borrow_pcg::edge_data::EdgeData;
use crate::borrow_pcg::{has_pcs_elem::HasPcgElems, region_projection::RegionProjection};
use crate::utils::json::ToJsonWithRepacker;

pub(crate) type BlockEdgeInputs<'tcx> = SmallVec<[PCGNode<'tcx>; 8]>;
pub(crate) type BlockEdgeOutputs<'tcx> = SmallVec<[LocalNode<'tcx>; 8]>;

/// A generic PCG hyperedge. `outputs` blocks `inputs`
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct BlockEdge<'tcx> {
    pub(crate) inputs: BlockEdgeInputs<'tcx>,
    pub(crate) outputs: BlockEdgeOutputs<'tcx>,
}

impl<'tcx> HasValidityCheck<'tcx> for BlockEdge<'tcx> {
    fn check_validity(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Result<(), String> {
        for input in self.inputs.iter() {
            input.check_validity(repacker)?;
        }
        for output in self.outputs.iter() {
            output.check_validity(repacker)?;
        }
        Ok(())
    }
}

impl<'tcx> DisplayWithRepacker<'tcx> for BlockEdge<'tcx> {
    fn to_short_string(&self, repacker: PlaceRepacker<'_, 'tcx>) -> String {
        format!(
            "{} -> {}",
            self.inputs
                .iter()
                .map(|p| p.to_short_string(repacker))
                .collect::<Vec<_>>()
                .join(", "),
            self.outputs
                .iter()
                .map(|p| p.to_short_string(repacker))
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

impl<'tcx> ToJsonWithRepacker<'tcx> for BlockEdge<'tcx> {
    fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        json!({
            "inputs": self.inputs.iter().map(|p| p.to_json(repacker)).collect::<Vec<_>>(),
            "outputs": self.outputs.iter().map(|p| p.to_json(repacker)).collect::<Vec<_>>(),
        })
    }
}

impl<'tcx> EdgeData<'tcx> for BlockEdge<'tcx> {
    fn blocked_by_nodes(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<LocalNode<'tcx>> {
        self.outputs.iter().cloned().collect()
    }

    fn blocked_nodes(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<PCGNode<'tcx>> {
        self.inputs.iter().cloned().collect()
    }

    fn is_owned_expansion(&self) -> bool {
        false
    }

    fn blocks_node(&self, node: BlockedNode<'tcx>, _repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        self.inputs.contains(&node)
    }
}

impl<'tcx> HasPcgElems<RegionProjection<'tcx>> for BlockEdge<'tcx> {
    fn pcg_elems(&mut self) -> Vec<&mut RegionProjection<'tcx>> {
        self.inputs.iter_mut().flat_map(|p| p.pcg_elems()).collect()
    }
}
impl<'tcx> HasPcgElems<RegionProjection<'tcx, MaybeOldPlace<'tcx>>> for BlockEdge<'tcx> {
    fn pcg_elems(&mut self) -> Vec<&mut RegionProjection<'tcx, MaybeOldPlace<'tcx>>> {
        self.outputs
            .iter_mut()
            .flat_map(|p| p.pcg_elems())
            .collect()
    }
}

impl<'tcx> HasPcgElems<MaybeOldPlace<'tcx>> for BlockEdge<'tcx> {
    fn pcg_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        self.inputs
            .iter_mut()
            .flat_map(|p| p.pcg_elems())
            .chain(self.outputs.iter_mut().flat_map(|p| p.pcg_elems()))
            .collect()
    }
}

impl<'tcx> BlockEdge<'tcx> {
    pub(crate) fn new(inputs: BlockEdgeInputs<'tcx>, outputs: BlockEdgeOutputs<'tcx>) -> Self {
        Self { inputs, outputs }
    }

    pub fn inputs(&self) -> &[PCGNode<'tcx>] {
        &self.inputs
    }

    pub fn outputs(&self) -> &[LocalNode<'tcx>] {
        &self.outputs
    }
}
