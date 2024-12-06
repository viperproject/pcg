use std::collections::HashSet;

use rustc_interface::{ast::Mutability, middle::mir::BasicBlock};

use crate::{
    borrows::{borrows_state::BorrowsState, domain::MaybeOldPlace, edge_data::EdgeData},
    combined_pcs::UnblockAction,
    rustc_interface,
    utils::PlaceRepacker,
    visualization::generate_unblock_dot_graph,
};

use super::{
    borrow_edge::BorrowEdge,
    borrow_pcg_edge::{BlockedNode, BorrowPCGEdge, BorrowPCGEdgeKind},
    domain::MaybeRemotePlace,
};

type UnblockEdge<'tcx> = BorrowPCGEdge<'tcx>;
type UnblockEdgeType<'tcx> = BorrowPCGEdgeKind<'tcx>;
#[derive(Clone, Debug)]
pub struct UnblockGraph<'tcx> {
    edges: HashSet<UnblockEdge<'tcx>>,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum UnblockHistoryAction<'tcx> {
    UnblockNode(BlockedNode<'tcx>),
    KillReborrow(BorrowEdge<'tcx>),
}

/// A history of the actions occurring in the construction of the unblock graph.
/// This should only be used for debugging
#[derive(Clone, Debug)]
pub struct UnblockHistory<'tcx>(Vec<UnblockHistoryAction<'tcx>>);

impl<'tcx> std::fmt::Display for UnblockHistory<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for action in self.0.iter() {
            match action {
                UnblockHistoryAction::UnblockNode(place) => {
                    writeln!(f, "unblock node {:?}", place)?;
                }
                UnblockHistoryAction::KillReborrow(reborrow) => {
                    writeln!(f, "kill reborrow {}", reborrow)?;
                }
            }
        }
        Ok(())
    }
}

impl<'tcx> UnblockHistory<'tcx> {
    pub fn new() -> Self {
        Self(vec![])
    }

    // Adds an element to the end of the history if it is not already present
    // Returns false iff the element was already present
    pub fn record(&mut self, action: UnblockHistoryAction<'tcx>) -> bool {
        if self.0.contains(&action) {
            false
        } else {
            self.0.push(action);
            true
        }
    }
}

impl<'tcx> UnblockGraph<'tcx> {
    pub fn edges(&self) -> impl Iterator<Item = &UnblockEdge<'tcx>> {
        self.edges.iter()
    }
    pub fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        let dot_graph = generate_unblock_dot_graph(&repacker, self).unwrap();
        serde_json::json!({
            "empty": self.is_empty(),
            "dot_graph": dot_graph
        })
    }

    pub fn new() -> Self {
        Self {
            edges: HashSet::new(),
        }
    }

    pub fn for_place(
        place: MaybeRemotePlace<'tcx>,
        state: &BorrowsState<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Self {
        let mut ug = Self::new();
        ug.unblock_node(place.into(), state, repacker);
        ug
    }

    pub fn is_empty(&self) -> bool {
        self.edges.is_empty()
    }

    pub fn filter_for_path(&mut self, path: &[BasicBlock]) {
        self.edges.retain(|edge| edge.valid_for_path(path));
    }

    pub fn actions(self, repacker: PlaceRepacker<'_, 'tcx>) -> Vec<UnblockAction<'tcx>> {
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
                    match edge.kind() {
                        UnblockEdgeType::Borrow(reborrow) => {
                            push_action(UnblockAction::TerminateBorrow {
                                blocked_place: reborrow.blocked_place,
                                assigned_place: reborrow.assigned_place,
                                reserve_location: reborrow.reserve_location(),
                                is_mut: reborrow.is_mut(),
                            });
                            to_keep.remove(edge);
                        }
                        UnblockEdgeType::DerefExpansion(deref_edge) => {
                            let expansion = deref_edge.expansion(repacker);
                            push_action(UnblockAction::Collapse(deref_edge.base(), expansion));
                            to_keep.remove(edge);
                        }
                        UnblockEdgeType::Abstraction(abstraction_edge) => {
                            push_action(UnblockAction::TerminateAbstraction(
                                abstraction_edge.location(),
                                abstraction_edge.abstraction_type.clone(),
                            ));
                            to_keep.remove(edge);
                        }
                        UnblockEdgeType::RegionProjectionMember(member) => {
                            // TODO: Action to remove the member
                            push_action(UnblockAction::TerminateRegionProjectionMember(
                                member.clone(),
                            ));
                            to_keep.remove(edge);
                        }
                    }
                }
            }
            assert!(
                to_keep.len() < edges.len(),
                "Didn't remove any leaves! {:#?}",
                edges
            );
            edges = to_keep;
        }
        actions
    }

    fn add_dependency(&mut self, unblock_edge: UnblockEdge<'tcx>) {
        self.edges.insert(unblock_edge);
    }

    fn report_error(&mut self) {
        panic!("Error in unblock graph");
    }

    pub fn kill_edge(
        &mut self,
        edge: BorrowPCGEdge<'tcx>,
        borrows: &BorrowsState<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) {
        self.add_dependency(edge.clone());
        for blocking_node in edge.blocked_by_nodes(repacker) {
            if !edge.is_owned_expansion() {
                self.unblock_node(blocking_node.into(), borrows, repacker);
            }
        }
    }

    pub fn unblock_node(
        &mut self,
        node: BlockedNode<'tcx>,
        borrows: &BorrowsState<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) {
        for edge in borrows.edges_blocking(node, repacker) {
            self.kill_edge(edge, borrows, repacker);
        }
        if let BlockedNode::Place(MaybeRemotePlace::Local(MaybeOldPlace::Current { place })) = node
        {
            for reborrow in borrows.borrows_blocking_prefix_of(place) {
                self.kill_edge(reborrow.into(), borrows, repacker);
            }
        }
    }
}
