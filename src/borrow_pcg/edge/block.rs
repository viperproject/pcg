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
use crate::borrow_pcg::{has_pcs_elem::HasPcsElems, region_projection::RegionProjection};
use crate::utils::json::ToJsonWithRepacker;

pub(crate) type BlockEdgeInputs<'tcx> = SmallVec<[PCGNode<'tcx>; 8]>;
pub(crate) type BlockEdgeOutputs<'tcx> = SmallVec<[LocalNode<'tcx>; 8]>;

/// A generic PCG hyperedge. `outputs` blocks `inputs`
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct BlockEdge<'tcx> {
    pub(crate) inputs: BlockEdgeInputs<'tcx>,
    pub(crate) outputs: BlockEdgeOutputs<'tcx>,
    /// Why this edge exists
    pub(crate) kind: BlockEdgeKind,
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

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub enum BlockEdgeKind {
    Aggregate {
        field_idx: usize,
        target_rp_index: usize,
    },
    /// Region projections resulting from a borrow
    Borrow,
    /// The input to the top-level function, in this case the inputs
    /// should only contain remote places
    FunctionInput,
    /// e.g. `t|'a -> *t`.
    DerefRegionProjection,
    /// e.g. x -> r|'a
    Ref,
    /// Region projection edge resulting due to contracting a place. For
    /// example, if the type of `x.t` is `&'a mut T` and there is a borrow `x.t
    /// = &mut y`, and we need to contract to `x`, then we need to replace the
    /// borrow edge with an edge `{y} -> {x↓'a}` of this kind.
    ContractRef,
    /// Connects a region projection from a constant to some PCG node. For
    /// example `let x: &'x C = c;` where `c` is a constant of type `&'c C`, then
    /// an edge `{c↓'c} -> {x↓'x}` of this kind is created.
    ConstRef,
    /// For a borrow `let x: &'x T<'b> = &y`, where y is of typ T<'a>, an edge generated
    /// for `{y|'a} -> {x|'b}` of this kind is created if 'a outlives 'b.
    ///
    /// `toplevel` is true for edges to x↓'x, false otherwise.
    BorrowOutlives { toplevel: bool },
    /// If e.g {x|'a} -> {y|'b} is a BorrowsOutlives, then {*x|'a} -> {*y|'b} is a DerefBorrowsOutlives
    /// (it's introduced if e.g. *y is expanded in the PCG)
    DerefBorrowOutlives,
    /// TODO: Provide more useful kinds, this enum variant should be removed
    Todo,
}

impl std::fmt::Display for BlockEdgeKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BlockEdgeKind::Aggregate {
                field_idx,
                target_rp_index,
            } => write!(f, "Aggregate({field_idx}, {target_rp_index})"),
            BlockEdgeKind::Borrow => write!(f, "Borrow"),
            BlockEdgeKind::FunctionInput => write!(f, "FunctionInput"),
            BlockEdgeKind::DerefRegionProjection => write!(f, "DerefRegionProjection"),
            BlockEdgeKind::Ref => write!(f, "Ref"),
            BlockEdgeKind::ContractRef => write!(f, "ContractRef"),
            BlockEdgeKind::ConstRef => write!(f, "ConstRef"),
            BlockEdgeKind::BorrowOutlives { toplevel } => write!(f, "BorrowOutlives({toplevel})"),
            BlockEdgeKind::Todo => write!(f, "Todo"),
            BlockEdgeKind::DerefBorrowOutlives => write!(f, "DerefBorrowOutlives"),
        }
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

impl<'tcx> HasPcsElems<RegionProjection<'tcx>> for BlockEdge<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut RegionProjection<'tcx>> {
        self.inputs.iter_mut().flat_map(|p| p.pcs_elems()).collect()
    }
}
impl<'tcx> HasPcsElems<RegionProjection<'tcx, MaybeOldPlace<'tcx>>> for BlockEdge<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut RegionProjection<'tcx, MaybeOldPlace<'tcx>>> {
        self.outputs
            .iter_mut()
            .flat_map(|p| p.pcs_elems())
            .collect()
    }
}

impl<'tcx> HasPcsElems<MaybeOldPlace<'tcx>> for BlockEdge<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        self.inputs
            .iter_mut()
            .flat_map(|p| p.pcs_elems())
            .chain(self.outputs.iter_mut().flat_map(|p| p.pcs_elems()))
            .collect()
    }
}

impl<'tcx> BlockEdge<'tcx> {

    pub(crate) fn new(
        inputs: BlockEdgeInputs<'tcx>,
        outputs: BlockEdgeOutputs<'tcx>,
        kind: BlockEdgeKind,
    ) -> Self {
        Self {
            inputs,
            outputs,
            kind,
        }
    }

    pub fn inputs(&self) -> &[PCGNode<'tcx>] {
        &self.inputs
    }

    pub fn outputs(&self) -> &[LocalNode<'tcx>] {
        &self.outputs
    }
}
