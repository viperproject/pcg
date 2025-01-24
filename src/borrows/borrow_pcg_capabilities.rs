use std::collections::HashMap;

use crate::{free_pcs::CapabilityKind, utils::Place};

use super::borrow_pcg_edge::PCGNode;

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

    pub(crate) fn debug_capability_lines(&self) -> Vec<String> {
        self.iter()
            .map(|(node, capability)| format!("{}: {:?}", node, capability))
            .collect()
    }

    /// Returns true iff the capability was changed.
    pub(super) fn insert<T: Into<PCGNode<'tcx>>>(
        &mut self,
        node: T,
        capability: CapabilityKind,
    ) -> bool {
        let node = node.into();
        self.0.insert(node, capability) != Some(capability)
    }

    pub(crate) fn remove<T: Into<PCGNode<'tcx>>>(&mut self, node: T) -> bool {
        let node = node.into();
        self.0.remove(&node).is_some()
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = (PCGNode<'tcx>, CapabilityKind)> + '_ {
        self.0.iter().map(|(k, v)| (k.clone(), v.clone()))
    }

    pub(crate) fn place_capabilities(
        &self,
    ) -> impl Iterator<Item = (Place<'tcx>, CapabilityKind)> + '_ {
        self.0
            .iter()
            .flat_map(|(k, v)| k.as_current_place().map(|p| (p, v.clone())))
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
