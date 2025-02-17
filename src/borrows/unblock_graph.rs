use std::collections::HashSet;

use crate::combined_pcs::PCGInternalError;
use crate::rustc_interface::middle::mir::BasicBlock;

use crate::{
    borrows::{borrows_state::BorrowsState, edge_data::EdgeData},
    combined_pcs::PCGNode,
    utils::PlaceRepacker,
    visualization::generate_unblock_dot_graph,
};
use crate::borrows::edge::kind::BorrowPCGEdgeKind;
use crate::utils::json::ToJsonWithRepacker;
use crate::utils::place::maybe_old::MaybeOldPlace;
use crate::utils::place::maybe_remote::MaybeRemotePlace;
use super::borrow_pcg_edge::BorrowPCGEdgeLike;
use super::borrow_pcg_edge::{BlockedNode, BorrowPCGEdge};

type UnblockEdge<'tcx> = BorrowPCGEdge<'tcx>;
type UnblockEdgeType<'tcx> = BorrowPCGEdgeKind<'tcx>;
#[derive(Clone, Debug)]
pub struct UnblockGraph<'tcx> {
    edges: HashSet<UnblockEdge<'tcx>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BorrowPCGUnblockAction<'tcx> {
    pub(super) edge: BorrowPCGEdge<'tcx>,
}

impl<'tcx> BorrowPCGUnblockAction<'tcx> {
    pub fn edge(&self) -> &BorrowPCGEdge<'tcx> {
        &self.edge
    }
}

impl<'tcx> ToJsonWithRepacker<'tcx> for BorrowPCGUnblockAction<'tcx> {
    fn to_json(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        serde_json::json!({
            "edge": format!("{:?}", self.edge)
        })
    }
}

impl<'tcx> From<BorrowPCGEdge<'tcx>> for BorrowPCGUnblockAction<'tcx> {
    fn from(edge: BorrowPCGEdge<'tcx>) -> Self {
        Self { edge }
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum UnblockType {
    ForRead,
    ForExclusive,
}

impl<'tcx> UnblockGraph<'tcx> {
    pub(crate) fn edges(&self) -> impl Iterator<Item = &UnblockEdge<'tcx>> {
        self.edges.iter()
    }

    #[allow(unused)]
    pub(crate) fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        let dot_graph = generate_unblock_dot_graph(&repacker, self).unwrap();
        serde_json::json!({
            "empty": self.is_empty(),
            "dot_graph": dot_graph
        })
    }

    pub(crate) fn new() -> Self {
        Self {
            edges: HashSet::new(),
        }
    }

    pub(crate) fn actions_to_unblock(
        node: PCGNode<'tcx>,
        state: &BorrowsState<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Result<Vec<BorrowPCGUnblockAction<'tcx>>, PCGInternalError> {
        let mut ug = UnblockGraph::new();
        ug.unblock_node(node, state, repacker, UnblockType::ForExclusive);
        ug.actions(repacker)
    }

    pub fn for_node(
        node: impl Into<BlockedNode<'tcx>>,
        state: &BorrowsState<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Self {
        let mut ug = Self::new();
        ug.unblock_node(node.into(), state, repacker, UnblockType::ForExclusive);
        ug
    }

    pub fn is_empty(&self) -> bool {
        self.edges.is_empty()
    }

    pub fn filter_for_path(&mut self, path: &[BasicBlock]) {
        self.edges.retain(|edge| edge.valid_for_path(path));
    }

    /// Returns an ordered list of actions to unblock the edges in the graph.
    /// This is essentially a topological sort of the edges.
    ///
    /// If this method returns an error, it is definitely a bug in the PCG
    /// implementation and should be reported.
    pub fn actions(
        self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Result<Vec<BorrowPCGUnblockAction<'tcx>>, PCGInternalError> {
        let mut edges = self.edges;
        let mut actions = vec![];

        // There might be duplicates because the same action may be required by
        // two unblocks in the graphs that occur for different reasons down this
        // path. TODO: Confirm that such graphs are actually valid
        let mut push_action = |action| {
            if !actions.contains(&action) {
                actions.push(action);
            }
        };

        while edges.len() > 0 {
            let mut to_keep = edges.clone();

            let should_kill_edge = |edge: &BorrowPCGEdge<'tcx>| {
                edge.blocked_by_nodes(repacker)
                    .into_iter()
                    .all(|node| edges.iter().all(|e| !e.blocks_node(node.into(), repacker)))
            };
            for edge in edges.iter() {
                if should_kill_edge(edge) {
                    push_action(BorrowPCGUnblockAction { edge: edge.clone() });
                    to_keep.remove(edge);
                }
            }
            if to_keep.len() >= edges.len() {
                return Err(PCGInternalError::new(format!(
                    "Didn't remove any leaves! {:#?}",
                    edges
                )));
            }
            edges = to_keep;
        }
        Ok(actions)
    }

    fn add_dependency(&mut self, unblock_edge: UnblockEdge<'tcx>) -> bool {
        self.edges.insert(unblock_edge)
    }

    pub(crate) fn kill_edge(
        &mut self,
        edge: impl BorrowPCGEdgeLike<'tcx>,
        borrows: &BorrowsState<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
        typ: UnblockType,
    ) {
        if let UnblockType::ForRead = typ {
            match edge.kind() {
                UnblockEdgeType::Borrow(reborrow) => {
                    if !reborrow.is_mut() {
                        return;
                    }
                    // Borrow is mutable, needs to be killed
                }
                _ => {
                    return;
                }
            }
        }
        if self.add_dependency(edge.clone().to_owned_edge()) {
            for blocking_node in edge.blocked_by_nodes(repacker) {
                if !edge.is_owned_expansion() {
                    // We always unblock for exclusive since the input edge is dead
                    self.unblock_node(
                        blocking_node.into(),
                        borrows,
                        repacker,
                        UnblockType::ForExclusive,
                    );
                }
            }
        }
    }

    pub(crate) fn unblock_node(
        &mut self,
        node: BlockedNode<'tcx>,
        borrows: &BorrowsState<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
        typ: UnblockType,
    ) {
        for edge in borrows.edges_blocking(node, repacker) {
            self.kill_edge(edge, borrows, repacker, typ);
        }
        if let BlockedNode::Place(MaybeRemotePlace::Local(MaybeOldPlace::Current { place })) = node
        {
            for reborrow in borrows.borrows_blocking_prefix_of(place) {
                let edge: BorrowPCGEdge<'tcx> = reborrow.into();
                self.kill_edge(edge, borrows, repacker, typ);
            }
        }
    }
}
