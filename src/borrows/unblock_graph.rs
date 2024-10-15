use std::collections::HashSet;

use rustc_interface::{
    ast::Mutability,
    middle::mir::{BasicBlock, Location},
};

use crate::{
    borrows::{
        borrows_edge::{ToBorrowsEdge},
        borrows_state::BorrowsState,
        domain::{MaybeOldPlace, Reborrow},
    },
    combined_pcs::UnblockAction,
    rustc_interface,
    utils::{PlaceRepacker, PlaceSnapshot},
    visualization::generate_unblock_dot_graph,
};

use super::{
    borrows_edge::{BorrowsEdge, BorrowsEdgeKind}, borrows_graph::Conditioned, domain::{AbstractionType, MaybeRemotePlace}, region_abstraction::AbstractionEdge
};

type UnblockEdge<'tcx> = BorrowsEdge<'tcx>;
type UnblockEdgeType<'tcx> = BorrowsEdgeKind<'tcx>;
#[derive(Clone, Debug)]
pub struct UnblockGraph<'tcx> {
    edges: HashSet<UnblockEdge<'tcx>>,

    /// For debugging only, record whether an error occurred
    error: bool,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum UnblockHistoryAction<'tcx> {
    UnblockPlace(MaybeRemotePlace<'tcx>),
    KillReborrow(Reborrow<'tcx>),
}

#[derive(Clone, Debug)]
pub struct UnblockHistory<'tcx>(Vec<UnblockHistoryAction<'tcx>>);

impl<'tcx> std::fmt::Display for UnblockHistory<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for action in self.0.iter() {
            match action {
                UnblockHistoryAction::UnblockPlace(place) => {
                    writeln!(f, "unblock place {}", place)?;
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

    pub fn has_error(&self) -> bool {
        self.error
    }
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
            error: false,
        }
    }

    pub fn for_place(
        place: MaybeRemotePlace<'tcx>,
        state: &BorrowsState<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Self {
        let mut ug = Self::new();
        ug.unblock_place(place, state, repacker);
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

            // A place is a leaf iff no other edge blocks it
            let is_leaf = |node| edges.iter().all(|e| !e.blocks_place(node));

            // A region is a leaf if no edge contains a region blocked by it,
            // and all places blocked by the region are leaves
            let is_leaf_abstraction = |abstraction: &AbstractionType<'tcx>| {
                abstraction
                    .blocker_places()
                    .iter()
                    .all(|place| is_leaf(*place))
                // && abstraction.blocker_regions.iter().all(|region_vid| {
                //     edges.iter().all(|e| match &e.edge_type {
                //         UnblockEdgeType::Abstraction(edge) => {
                //             edge.location() != abstraction.location()
                //         }
                //         _ => true,
                //     })
                // })
            };
            for edge in edges.iter() {
                match edge.kind() {
                    UnblockEdgeType::Reborrow(reborrow) => {
                        if is_leaf(reborrow.assigned_place) {
                            push_action(UnblockAction::TerminateReborrow {
                                blocked_place: reborrow.blocked_place,
                                assigned_place: reborrow.assigned_place,
                                reserve_location: reborrow.reserve_location(),
                                is_mut: reborrow.mutability == Mutability::Mut,
                            });
                            to_keep.remove(edge);
                        }
                    }
                    UnblockEdgeType::DerefExpansion(deref_edge) => {
                        let expansion = deref_edge.expansion(repacker);
                        if expansion.iter().all(|p| is_leaf(*p)) {
                            push_action(UnblockAction::Collapse(deref_edge.base(), expansion));
                            to_keep.remove(edge);
                        }
                    }
                    UnblockEdgeType::Abstraction(abstraction_edge) => {
                        if is_leaf_abstraction(&abstraction_edge.abstraction_type) {
                            push_action(UnblockAction::TerminateAbstraction(
                                abstraction_edge.location(),
                                abstraction_edge.abstraction_type.clone(),
                            ));
                            to_keep.remove(edge);
                        }
                    }
                    _ => {}
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

    pub fn kill_abstraction(
        &mut self,
        borrows: &BorrowsState<'tcx>,
        abstraction: Conditioned<AbstractionEdge<'tcx>>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) {
        for place in &abstraction.value.blocks_places() {
            match place {
                MaybeRemotePlace::Local(MaybeOldPlace::OldPlace(p)) => {
                    self.trim_old_leaves_from(borrows, p.clone(), repacker)
                }
                _ => {}
            }
        }
        self.add_dependency(abstraction.to_borrows_edge());
    }
    pub fn unblock_place(
        &mut self,
        place: MaybeRemotePlace<'tcx>,
        borrows: &BorrowsState<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) {
        self.unblock_place_internal(place, borrows, repacker, UnblockHistory::new());
    }

    fn report_error(&mut self) {
        panic!("Error in unblock graph");
        // self.error = true;
    }

    fn unblock_place_internal(
        &mut self,
        place: MaybeRemotePlace<'tcx>,
        borrows: &BorrowsState<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
        mut history: UnblockHistory<'tcx>,
    ) {
        if !history.record(UnblockHistoryAction::UnblockPlace(place)) {
            self.report_error();
            return;
        }
        for edge in borrows.edges_blocking(place) {
            match edge.kind() {
                BorrowsEdgeKind::Reborrow(reborrow) => self.kill_reborrow_internal(
                    Conditioned::new(reborrow.clone(), edge.conditions().clone()),
                    borrows,
                    repacker,
                    history.clone(),
                ),
                BorrowsEdgeKind::DerefExpansion(expansion) => {
                    self.add_dependency(edge.clone());
                    for place in expansion.expansion(repacker) {
                        self.unblock_place_internal(
                            place.into(),
                            borrows,
                            repacker,
                            history.clone(),
                        );
                    }
                }
                BorrowsEdgeKind::Abstraction(abstraction) => {
                    for place in abstraction.abstraction_type.blocker_places() {
                        self.unblock_place_internal(
                            place.into(),
                            borrows,
                            repacker,
                            history.clone(),
                        );
                    }
                    self.add_dependency(edge.clone());
                }
                BorrowsEdgeKind::RegionProjectionMember(_) => {
                    // TODO
                }
            }
        }
    }

    pub fn kill_reborrows_reserved_at(
        &mut self,
        location: Location,
        borrows: &BorrowsState<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) {
        for edge in borrows.reborrow_edges_reserved_at(location) {
                self.unblock_place(edge.value.assigned_place.into(), borrows, repacker);
                self.add_dependency(edge.to_borrows_edge());
        }
    }

    pub fn kill_reborrow_internal(
        &mut self,
        reborrow: Conditioned<Reborrow<'tcx>>,
        borrows: &BorrowsState<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
        mut history: UnblockHistory<'tcx>,
    ) {
        if !history.record(UnblockHistoryAction::KillReborrow(reborrow.value.clone())) {
            self.error = true;
            return;
        }
        self.unblock_place_internal(
            reborrow.value.assigned_place.into(),
            borrows,
            repacker,
            history,
        );
        self.add_dependency(reborrow.to_borrows_edge());
    }

    pub fn kill_reborrow(
        &mut self,
        reborrow: Conditioned<Reborrow<'tcx>>,
        borrows: &BorrowsState<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) {
        self.kill_reborrow_internal(reborrow, borrows, repacker, UnblockHistory::new());
    }

    pub fn trim_old_leaves_from(
        &mut self,
        borrows: &BorrowsState<'tcx>,
        place: PlaceSnapshot<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) {
        for reborrow in borrows.reborrows_blocked_by(MaybeOldPlace::OldPlace(place)) {
            match reborrow.value.blocked_place {
                MaybeRemotePlace::Local(MaybeOldPlace::OldPlace(p)) => {
                    self.trim_old_leaves_from(borrows, p.clone(), repacker)
                }
                _ => {}
            }
            self.kill_reborrow(reborrow, borrows, repacker);
        }
    }
}
