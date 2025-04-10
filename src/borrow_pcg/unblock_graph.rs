use std::collections::HashSet;

use crate::pcg::PCGInternalError;
use crate::rustc_interface::middle::mir::BasicBlock;

use super::borrow_pcg_edge::BorrowPCGEdgeLike;
use super::borrow_pcg_edge::{BlockedNode, BorrowPCGEdge};
use crate::utils::json::ToJsonWithCompilerCtxt;
use crate::{
    borrow_pcg::{edge_data::EdgeData, state::BorrowsState},
    utils::CompilerCtxt,
};

type UnblockEdge<'tcx> = BorrowPCGEdge<'tcx>;
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

impl<'tcx> ToJsonWithCompilerCtxt<'tcx> for BorrowPCGUnblockAction<'tcx> {
    fn to_json(&self, _repacker: CompilerCtxt<'_, 'tcx,'_>) -> serde_json::Value {
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

impl<'tcx> UnblockGraph<'tcx> {
    pub(crate) fn new() -> Self {
        Self {
            edges: HashSet::new(),
        }
    }

    pub fn for_node(
        node: impl Into<BlockedNode<'tcx>>,
        state: &BorrowsState<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx,'_>,
    ) -> Self {
        let mut ug = Self::new();
        ug.unblock_node(node.into(), state, repacker);
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
        repacker: CompilerCtxt<'_, 'tcx,'_>,
    ) -> Result<Vec<BorrowPCGUnblockAction<'tcx>>, PCGInternalError> {
        let mut edges = self.edges;
        let mut actions = vec![];

        while !edges.is_empty() {
            let mut to_keep = edges.clone();

            let should_kill_edge = |edge: &BorrowPCGEdge<'tcx>| {
                edge.blocked_by_nodes(repacker)
                    .into_iter()
                    .all(|node| edges.iter().all(|e| !e.blocks_node(node.into(), repacker)))
            };
            for edge in edges.iter() {
                if should_kill_edge(edge) {
                    actions.push(BorrowPCGUnblockAction { edge: edge.clone() });
                    to_keep.remove(edge);
                }
            }
            if to_keep.len() >= edges.len() {
                return Err(PCGInternalError::new(format!(
                    "Didn't remove any leaves {:#?}",
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
        repacker: CompilerCtxt<'_, 'tcx,'_>,
    ) {
        if self.add_dependency(edge.clone().to_owned_edge()) {
            for blocking_node in edge.blocked_by_nodes(repacker) {
                self.unblock_node(blocking_node.into(), borrows, repacker);
            }
        }
    }

    #[tracing::instrument(skip(self, borrows, repacker))]
    pub fn unblock_node(
        &mut self,
        node: BlockedNode<'tcx>,
        borrows: &BorrowsState<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx,'_>,
    ) {
        for edge in borrows.edges_blocking(node, repacker) {
            self.kill_edge(edge, borrows, repacker);
        }
    }
}
