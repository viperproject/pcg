use std::collections::HashSet;

use rustc_interface::middle::mir::BasicBlock;

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

#[derive(Clone, Copy, Debug)]
pub(crate) enum UnblockType {
    ForRead,
    ForExclusive,
}

impl<'tcx> UnblockGraph<'tcx> {
    pub (crate) fn edges(&self) -> impl Iterator<Item = &UnblockEdge<'tcx>> {
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
        ug.unblock_node(place.into(), state, repacker, UnblockType::ForExclusive);
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

    pub(crate) fn kill_edge(
        &mut self,
        edge: BorrowPCGEdge<'tcx>,
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
        self.add_dependency(edge.clone());
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
                self.kill_edge(reborrow.into(), borrows, repacker, typ);
            }
        }
    }
}
