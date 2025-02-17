use serde_json::json;
use smallvec::SmallVec;

use crate::combined_pcs::PCGNode;
use crate::pcg_validity_assert;
use crate::rustc_interface::{ast::Mutability, data_structures::fx::FxHashSet};
use crate::utils::display::DisplayWithRepacker;
use crate::utils::place::maybe_old::MaybeOldPlace;
use crate::utils::validity::HasValidityCheck;
use crate::utils::PlaceRepacker;

use super::borrow_pcg_edge::{BlockedNode, LocalNode};
use super::edge_data::EdgeData;
use super::{has_pcs_elem::HasPcsElems, region_projection::RegionProjection};
use crate::utils::json::ToJsonWithRepacker;

pub(crate) type RegionProjectionMemberInputs<'tcx> = SmallVec<[PCGNode<'tcx>; 8]>;
pub(crate) type RegionProjectionMemberOutputs<'tcx> = SmallVec<[LocalNode<'tcx>; 8]>;

/// A PCG hyperedge where at the nodes of at least one of the edge endpoints are
/// all region projections.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct RegionProjectionMember<'tcx> {
    pub(crate) inputs: RegionProjectionMemberInputs<'tcx>,
    pub(crate) outputs: RegionProjectionMemberOutputs<'tcx>,
    pub(crate) kind: RegionProjectionMemberKind,
}

impl<'tcx> HasValidityCheck<'tcx> for RegionProjectionMember<'tcx> {
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

impl<'tcx> DisplayWithRepacker<'tcx> for RegionProjectionMember<'tcx> {
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
pub enum RegionProjectionMemberKind {
    Aggregate {
        field_idx: usize,
        target_rp_index: usize,
    },
    /// Region projections resulting from a borrow
    Borrow,
    /// The input to the top-level function, in this case the inputs
    /// should only contain remote places
    FunctionInput,
    /// e.g. t|'a -> *t
    DerefRegionProjection,
    /// e.g. x -> r|'a
    Ref,
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

    fn blocks_node(&self, node: BlockedNode<'tcx>, _repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        self.inputs.contains(&node)
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
        let mut_values = self
            .inputs
            .iter()
            .map(|p| p.mutability(repacker))
            .collect::<Vec<_>>();
        pcg_validity_assert!(
            mut_values.windows(2).all(|w| w[0] == w[1]),
            "All mutability values must be the same"
        );
        mut_values[0]
    }

    pub(crate) fn new(
        inputs: RegionProjectionMemberInputs<'tcx>,
        outputs: RegionProjectionMemberOutputs<'tcx>,
        kind: RegionProjectionMemberKind,
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
