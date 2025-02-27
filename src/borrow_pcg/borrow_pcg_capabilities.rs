use itertools::Itertools;

use crate::{
    combined_pcs::PCGNode,
    free_pcs::CapabilityKind,
    rustc_interface::data_structures::fx::FxHashMap,
    utils::{
        display::{DebugLines, DisplayWithRepacker},
        PlaceRepacker,
    },
};

/// Tracks the capabilities of places in the borrow PCG. We don't store this
/// information in the borrows graph directly to facilitate simpler logic for
/// joins (in particular, to identify when capabilities to a place in the PCG
/// need to be weakened).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BorrowPCGCapabilities<'tcx>(FxHashMap<PCGNode<'tcx>, CapabilityKind>);

impl<'tcx> DebugLines<PlaceRepacker<'_, 'tcx>> for BorrowPCGCapabilities<'tcx> {
    fn debug_lines(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Vec<String> {
        self.iter()
            .map(|(node, capability)| {
                format!("{}: {:?}", node.to_short_string(repacker), capability)
            })
            .sorted()
            .collect()
    }
}

impl<'tcx> BorrowPCGCapabilities<'tcx> {
    pub(crate) fn new() -> Self {
        Self(Default::default())
    }

    /// Returns true iff the capability was changed.
    pub(super) fn insert(&mut self, node: PCGNode<'tcx>, capability: CapabilityKind) -> bool {
        self.0.insert(node, capability) != Some(capability)
    }

    pub(crate) fn remove(&mut self, node: PCGNode<'tcx>) -> bool {
        self.0.remove(&node).is_some()
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = (PCGNode<'tcx>, CapabilityKind)> + '_ {
        self.0.iter().map(|(k, v)| (*k, *v))
    }

    pub(crate) fn get<T: Into<PCGNode<'tcx>>>(&self, node: T) -> Option<CapabilityKind> {
        self.0.get(&node.into()).copied()
    }

    pub(crate) fn join(&mut self, other: &Self) -> bool {
        let mut changed = false;
        for (place, other_capability) in other.iter() {
            match self.0.get(&place) {
                Some(self_capability) => {
                    if let Some(c) = self_capability.minimum(other_capability) {
                        changed |= self.0.insert(place, c) != Some(c);
                    } else {
                        self.0.remove(&place);
                        changed = true;
                    }
                }
                None => {
                    self.0.insert(place, other_capability);
                    changed = true;
                }
            }
        }
        changed
    }
}
