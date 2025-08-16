//! Data structures and algorithms related to [`UnblockGraph`].
use std::collections::HashSet;

use derive_more::From;

use crate::borrow_checker::BorrowCheckerInterface;
use crate::error::PcgInternalError;

use super::borrow_pcg_edge::BorrowPcgEdgeLike;
use super::borrow_pcg_edge::{BlockedNode, BorrowPcgEdge};
use crate::utils::json::ToJsonWithCompilerCtxt;
use crate::{
    borrow_pcg::{edge_data::EdgeData, state::BorrowsState},
    utils::CompilerCtxt,
};

type UnblockEdge<'tcx> = BorrowPcgEdge<'tcx>;

/// A subgraph of the Borrow PCG including the edges that should be removed
/// in order to unblock a given node.
#[derive(Clone, Debug)]
pub struct UnblockGraph<'tcx> {
    edges: HashSet<UnblockEdge<'tcx>>,
}

/// An action that removes an edge from the Borrow PCG
#[derive(Clone, Debug, Eq, PartialEq, From)]
pub struct BorrowPcgUnblockAction<'tcx> {
    pub(super) edge: BorrowPcgEdge<'tcx>,
}

impl<'tcx> BorrowPcgUnblockAction<'tcx> {
    pub fn edge(&self) -> &BorrowPcgEdge<'tcx> {
        &self.edge
    }
}

impl<'tcx, 'a> ToJsonWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>
    for BorrowPcgUnblockAction<'tcx>
{
    fn to_json(
        &self,
        _repacker: CompilerCtxt<'_, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    ) -> serde_json::Value {
        serde_json::json!({
            "edge": format!("{:?}", self.edge)
        })
    }
}

impl<'tcx> UnblockGraph<'tcx> {
    pub(crate) fn new() -> Self {
        Self {
            edges: HashSet::new(),
        }
    }

    pub fn for_node(
        node: impl Into<BlockedNode<'tcx>>,
        state: &BorrowsState<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> Self {
        let mut ug = Self::new();
        ug.unblock_node(node.into(), state, repacker);
        ug
    }

    pub fn is_empty(&self) -> bool {
        self.edges.is_empty()
    }

    /// Returns an ordered list of actions to unblock the edges in the graph.
    /// This is essentially a topological sort of the edges.
    ///
    /// This method could fail if the If this method returns an error, it should be reported.
    pub fn actions(
        self,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> Result<Vec<BorrowPcgUnblockAction<'tcx>>, PcgInternalError> {
        let mut edges = self.edges;
        let mut actions = vec![];

        while !edges.is_empty() {
            let mut to_keep = edges.clone();

            let should_kill_edge = |edge: &BorrowPcgEdge<'tcx>| {
                edge.blocked_by_nodes(repacker)
                    .all(|node| edges.iter().all(|e| !e.blocks_node(node.into(), repacker)))
            };
            for edge in edges.iter() {
                if should_kill_edge(edge) {
                    actions.push(BorrowPcgUnblockAction::from(edge.clone()));
                    to_keep.remove(edge);
                }
            }
            if to_keep.len() >= edges.len() {
                return Err(PcgInternalError::new(format!(
                    "Didn't remove any leaves {edges:#?}"
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
        edge: impl BorrowPcgEdgeLike<'tcx>,
        borrows: &BorrowsState<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) {
        if self.add_dependency(edge.clone().to_owned_edge()) {
            for blocking_node in edge.blocked_by_nodes(repacker) {
                self.unblock_node(blocking_node.into(), borrows, repacker);
            }
        }
    }

    #[tracing::instrument(skip(self, borrows, repacker))]
    pub(crate) fn unblock_node(
        &mut self,
        node: BlockedNode<'tcx>,
        borrows: &BorrowsState<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) {
        for edge in borrows.edges_blocking(node, repacker) {
            self.kill_edge(edge, borrows, repacker);
        }
    }
}
