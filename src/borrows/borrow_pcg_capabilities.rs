use std::collections::HashMap;

use crate::{
    combined_pcs::{PCGNode, PCGNodeLike},
    free_pcs::CapabilityKind,
    utils::{display::DisplayWithRepacker, PlaceRepacker},
};

/// Tracks the capabilities of places in the borrow PCG. We don't store this
/// information in the borrows graph directly to facilitate simpler logic for
/// joins (in particular, to identify when capabilities to a place in the PCG
/// need to be weakened).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BorrowPCGCapabilities<'tcx>(HashMap<PCGNode<'tcx>, CapabilityKind>);

impl<'tcx> BorrowPCGCapabilities<'tcx> {
    pub(crate) fn new() -> Self {
        Self(HashMap::new())
    }

    pub(crate) fn debug_capability_lines(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Vec<String> {
        self.iter()
            .map(|(node, capability)| {
                format!("{}: {:?}", node.to_short_string(repacker), capability)
            })
            .collect()
    }

    /// Returns true iff the capability was changed.
    pub(super) fn insert<T: PCGNodeLike<'tcx>>(
        &mut self,
        node: T,
        capability: CapabilityKind,
    ) -> bool {
        self.0.insert(node.to_pcg_node(), capability) != Some(capability)
    }

    pub(crate) fn remove<T: PCGNodeLike<'tcx>>(&mut self, node: T) -> bool {
        let node = node.to_pcg_node();
        self.0.remove(&node).is_some()
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = (PCGNode<'tcx>, CapabilityKind)> + '_ {
        self.0.iter().map(|(k, v)| (k.clone(), v.clone()))
    }

    pub(crate) fn get<T: Into<PCGNode<'tcx>>>(&self, node: T) -> Option<CapabilityKind> {
        self.0.get(&node.into()).cloned()
    }

    /// TODO: The logic here isn't quite right yet.
    pub(crate) fn join(&mut self, other: &Self) -> bool {
        let mut changed = false;
        for (place, capability) in other.iter() {
            if self.0.insert(place, capability).is_none() {
                changed = true;
            }
        }
        changed
    }
}
