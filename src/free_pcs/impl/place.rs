// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use derive_more::Deref;
use std::{
    cmp::Ordering,
    fmt::{Debug, Formatter, Result},
};

use rustc_interface::data_structures::fx::FxHashSet;

use crate::{rustc_interface, utils::Place};

#[derive(Debug, Deref)]
pub(crate) struct RelatedSet<'tcx>(FxHashSet<(Place<'tcx>, CapabilityKind)>);

impl<'tcx> RelatedSet<'tcx> {
    pub fn new(related: FxHashSet<(Place<'tcx>, CapabilityKind)>) -> Self {
        Self(related)
    }
    pub fn get_places(&self) -> FxHashSet<Place<'tcx>> {
        self.0.iter().map(|(p, _)| *p).collect()
    }
    pub fn get_only_place(&self) -> Place<'tcx> {
        assert_eq!(self.0.len(), 1);
        self.0.iter().next().unwrap().0
    }
    pub fn common_prefix(&self, to: Place<'tcx>) -> Place<'tcx> {
        self.get_places()
            .iter()
            .fold(to, |acc, p| acc.common_prefix(*p))
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum CapabilityKind {
    /// For borrowed places only: permits reads from the location, but not writes or
    /// drops.
    Read,

    /// For owned places, this capability is used when the place is moved out
    /// of. This capability is used for both owned and borrowed places just before
    /// they are overwritten.
    Write,

    /// Writes and reads are permitted to this place, and the place is not
    /// borrowed.
    Exclusive,

    /// This place is mutably borrowed.
    Lent,

    /// There are outstanding shared borrows to this place or to projections of
    /// this place. The capability to the place can be restored to
    /// [`CapabilityKind::Exclusive`] in exchange for the capabilities of its
    /// projections when the borrows expire.
    LentShared,

    /// [`CapabilityKind::Exclusive`] for everything not through a dereference,
    /// [`CapabilityKind::Write`] for everything through a dereference.
    ShallowExclusive,
}
impl Debug for CapabilityKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            CapabilityKind::Read => write!(f, "R"),
            CapabilityKind::Write => write!(f, "W"),
            CapabilityKind::Exclusive => write!(f, "E"),
            CapabilityKind::ShallowExclusive => write!(f, "e"),
            CapabilityKind::Lent => write!(f, "L"),
            CapabilityKind::LentShared => write!(f, "Ls"),
        }
    }
}

impl PartialOrd for CapabilityKind {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if *self == *other {
            return Some(Ordering::Equal);
        }
        match (*self, *other) {
            // Exclusive is greater than everything below it
            (CapabilityKind::Exclusive, CapabilityKind::ShallowExclusive) => {
                Some(Ordering::Greater)
            }
            (CapabilityKind::Exclusive, CapabilityKind::LentShared) => Some(Ordering::Greater),
            (CapabilityKind::ShallowExclusive, CapabilityKind::Exclusive) => Some(Ordering::Less),
            (CapabilityKind::LentShared, CapabilityKind::Exclusive) => Some(Ordering::Less),

            // ShallowExclusive > Write
            (CapabilityKind::ShallowExclusive, CapabilityKind::Write) => Some(Ordering::Greater),
            (CapabilityKind::Write, CapabilityKind::ShallowExclusive) => Some(Ordering::Less),

            // LentShared > {Lent, Read}
            (CapabilityKind::LentShared, CapabilityKind::Lent) => Some(Ordering::Greater),
            (CapabilityKind::LentShared, CapabilityKind::Read) => Some(Ordering::Greater),
            (CapabilityKind::Lent, CapabilityKind::LentShared) => Some(Ordering::Less),
            (CapabilityKind::Read, CapabilityKind::LentShared) => Some(Ordering::Less),

            // Transitive relationships through ShallowExclusive
            (CapabilityKind::Exclusive, CapabilityKind::Write) => Some(Ordering::Greater),
            (CapabilityKind::Write, CapabilityKind::Exclusive) => Some(Ordering::Less),

            // Transitive relationships through LentShared
            (CapabilityKind::Exclusive, CapabilityKind::Lent) => Some(Ordering::Greater),
            (CapabilityKind::Exclusive, CapabilityKind::Read) => Some(Ordering::Greater),
            (CapabilityKind::Lent, CapabilityKind::Exclusive) => Some(Ordering::Less),
            (CapabilityKind::Read, CapabilityKind::Exclusive) => Some(Ordering::Less),

            // All other pairs are incomparable
            _ => None,
        }
    }
}

impl CapabilityKind {
    pub fn is_exclusive(self) -> bool {
        matches!(self, CapabilityKind::Exclusive)
    }
    pub fn is_lent_exclusive(self) -> bool {
        matches!(self, CapabilityKind::Lent)
    }
    pub fn is_read(self) -> bool {
        matches!(self, CapabilityKind::Read)
    }
    pub fn is_write(self) -> bool {
        matches!(self, CapabilityKind::Write)
    }
    pub fn is_shallow_exclusive(self) -> bool {
        matches!(self, CapabilityKind::ShallowExclusive)
    }

    pub fn minimum(self, other: Self) -> Option<Self> {
        match self.partial_cmp(&other) {
            Some(Ordering::Greater) => Some(other),
            Some(Ordering::Less) => Some(self),
            Some(Ordering::Equal) => Some(self),
            None => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    #[test]
    fn test_capability_kind_dag_reachability() {
        use petgraph::algo::has_path_connecting;
        use petgraph::graph::DiGraph;

        // Create directed graph
        let mut graph = DiGraph::new();
        let mut node_indices = HashMap::new();

        let caps = [
            CapabilityKind::Exclusive,
            CapabilityKind::ShallowExclusive,
            CapabilityKind::Write,
            CapabilityKind::Read,
            CapabilityKind::LentShared,
            CapabilityKind::Lent,
        ];
        // Add nodes
        for cap in caps {
            node_indices.insert(cap, graph.add_node(cap));
        }

        // Add edges (a -> b means a is greater than b)
        let edges = [
            (CapabilityKind::Exclusive, CapabilityKind::ShallowExclusive),
            (CapabilityKind::Exclusive, CapabilityKind::LentShared),
            (CapabilityKind::ShallowExclusive, CapabilityKind::Write),
            (CapabilityKind::LentShared, CapabilityKind::Lent),
            (CapabilityKind::LentShared, CapabilityKind::Read),
        ];

        for (from, to) in edges {
            graph.add_edge(node_indices[&from], node_indices[&to], ());
        }

        // Test that partial_cmp matches graph reachability
        for a in caps {
            for b in caps {
                if a == b {
                    assert!(a.partial_cmp(&b) == Some(Ordering::Equal));
                } else if has_path_connecting(&graph, node_indices[&a], node_indices[&b], None) {
                    assert!(a.partial_cmp(&b) == Some(Ordering::Greater));
                } else if has_path_connecting(&graph, node_indices[&b], node_indices[&a], None) {
                    assert!(a.partial_cmp(&b) == Some(Ordering::Less));
                } else {
                    assert!(a.partial_cmp(&b).is_none());
                }
            }
        }
    }
}
