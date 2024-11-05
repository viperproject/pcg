use rustc_interface::{
    ast::Mutability,
    borrowck::consumers::{LocationTable, PoloniusOutput},
    data_structures::fx::FxHashSet,
    middle::mir::{self, BasicBlock, Location},
    middle::ty::{self, TyCtxt},
};
use serde_json::{json, Value};

use crate::{
    free_pcs::{CapabilityKind, CapabilityLocal, CapabilitySummary},
    rustc_interface,
    utils::{Place, PlaceRepacker, SnapshotLocation},
    BorrowsBridge,
};

use super::{
    borrows_edge::{BlockedNode, BorrowsEdge, BorrowsEdgeKind, ToBorrowsEdge},
    borrows_graph::{BorrowsGraph, Conditioned},
    borrows_visitor::DebugCtx,
    coupling_graph_constructor::LivenessChecker,
    deref_expansion::DerefExpansion,
    domain::{Borrow, MaybeOldPlace, MaybeRemotePlace},
    has_pcs_elem::HasPcsElems,
    latest::Latest,
    path_condition::{PathCondition, PathConditions},
    region_abstraction::AbstractionEdge,
    region_projection_member::{RegionProjectionMember, RegionProjectionMemberDirection},
    unblock_graph::UnblockGraph,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BorrowsState<'tcx> {
    pub latest: Latest<'tcx>,
    graph: BorrowsGraph<'tcx>,
}

impl<'tcx> BorrowsState<'tcx> {
    pub fn graph(&self) -> &BorrowsGraph<'tcx> {
        &self.graph
    }

    pub fn join<'mir, T: LivenessChecker<'tcx>>(
        &mut self,
        other: &Self,
        self_block: BasicBlock,
        other_block: BasicBlock,
        region_liveness: &T,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        let mut changed = false;
        if self.graph.join(
            &other.graph,
            self_block,
            other_block,
            repacker,
            region_liveness,
        ) {
            changed = true;
        }
        if self.latest.join(&other.latest, self_block) {
            // TODO: Setting changed to true prevents divergence for loops,
            // think about how latest should work in loops

            // changed = true;
        }
        changed
    }

    pub fn change_pcs_elem<T: 'tcx>(&mut self, old: T, new: T) -> bool
    where
        T: PartialEq + Clone,
        BorrowsEdge<'tcx>: HasPcsElems<T>,
    {
        self.graph.change_pcs_elem(old, new)
    }

    pub fn remove_edge_and_set_latest(
        &mut self,
        edge: &BorrowsEdge<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
        location: Location,
    ) -> bool {
        if !edge.is_shared_borrow() {
            for place in edge.blocked_places(repacker) {
                match place {
                    MaybeRemotePlace::Local(MaybeOldPlace::Current { place }) => {
                        self.set_latest(place, location)
                    }
                    _ => {}
                }
            }
        }
        self.graph.remove(edge, DebugCtx::new(location))
    }

    pub fn reborrow_edges_reserved_at(
        &self,
        location: Location,
    ) -> FxHashSet<Conditioned<Borrow<'tcx>>> {
        self.graph
            .edges()
            .filter_map(|edge| match &edge.kind() {
                BorrowsEdgeKind::Reborrow(reborrow) if reborrow.reserve_location() == location => {
                    Some(Conditioned {
                        conditions: edge.conditions().clone(),
                        value: reborrow.clone(),
                    })
                }
                _ => None,
            })
            .collect()
    }

    /// Collapses nodes using the following rules:
    /// - If a node is only blocked by old leaves, then the node should be collapsed
    /// - If a PCS node's expansion is only leaves, the node should be collapsed
    /// This function performs such collapses until a fixpoint is reached
    pub fn minimize(&mut self, repacker: PlaceRepacker<'_, 'tcx>, location: Location) {
        loop {
            let to_remove = self
                .graph
                .edges()
                .filter(|edge| {
                    let is_old_unblocked = edge
                        .blocked_by_nodes(repacker)
                        .iter()
                        .all(|p| p.is_old() && !self.graph.has_edge_blocking(repacker, *p));
                    is_old_unblocked
                        || match &edge.kind() {
                            BorrowsEdgeKind::DerefExpansion(de) => {
                                !de.is_owned_expansion()
                                    && de
                                        .expansion(repacker)
                                        .into_iter()
                                        .all(|p| !self.graph.has_edge_blocking(repacker, p))
                            }
                            _ => false,
                        }
                })
                .cloned()
                .collect::<Vec<_>>();
            if to_remove.is_empty() {
                break;
            }
            for edge in to_remove {
                self.remove_edge_and_set_latest(&edge, repacker, location);
            }
        }
    }

    pub fn add_path_condition(&mut self, pc: PathCondition) -> bool {
        self.graph.add_path_condition(pc)
    }

    pub fn filter_for_path(&mut self, path: &[BasicBlock]) {
        self.graph.filter_for_path(path);
    }

    pub fn reborrows_blocking_prefix_of(
        &self,
        place: Place<'tcx>,
    ) -> FxHashSet<Conditioned<Borrow<'tcx>>> {
        self.reborrows()
            .into_iter()
            .filter(|rb| match rb.value.blocked_place {
                MaybeRemotePlace::Local(MaybeOldPlace::Current {
                    place: blocked_place,
                }) => blocked_place.is_prefix(place),
                _ => false,
            })
            .collect()
    }

    pub fn delete_descendants_of(
        &mut self,
        place: MaybeOldPlace<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
        location: Location,
    ) -> bool {
        let edges = self.edges_blocking(place.into(), repacker);
        if edges.is_empty() {
            return false;
        }
        for edge in edges {
            self.remove_edge_and_set_latest(&edge, repacker, location);
        }
        true
    }

    pub fn get_place_blocking(
        &self,
        place: MaybeRemotePlace<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Option<MaybeOldPlace<'tcx>> {
        let edges = self.edges_blocking(place.into(), repacker);
        if edges.len() != 1 {
            return None;
        }
        match edges[0].kind() {
            BorrowsEdgeKind::Reborrow(reborrow) => Some(reborrow.assigned_place),
            BorrowsEdgeKind::DerefExpansion(_) => todo!(),
            BorrowsEdgeKind::Abstraction(_) => todo!(),
            BorrowsEdgeKind::RegionProjectionMember(_) => todo!(),
        }
    }

    pub fn edges_blocking(
        &self,
        node: BlockedNode<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Vec<BorrowsEdge<'tcx>> {
        self.graph.edges_blocking(node, repacker)
    }

    pub fn graph_edges(&self) -> impl Iterator<Item = &BorrowsEdge<'tcx>> {
        self.graph.edges()
    }

    pub fn deref_expansions(&self) -> FxHashSet<Conditioned<DerefExpansion<'tcx>>> {
        self.graph.deref_expansions()
    }

    pub fn move_region_projection_member_projections(
        &mut self,
        old_projection_place: MaybeOldPlace<'tcx>,
        new_projection_place: MaybeOldPlace<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) {
        self.graph.move_region_projection_member_projections(
            old_projection_place,
            new_projection_place,
            repacker,
        );
    }

    pub fn move_reborrows(
        &mut self,
        orig_assigned_place: MaybeOldPlace<'tcx>,
        new_assigned_place: MaybeOldPlace<'tcx>,
    ) {
        self.graph
            .move_reborrows(orig_assigned_place, new_assigned_place);
    }

    pub fn reborrows_blocked_by(
        &self,
        place: MaybeOldPlace<'tcx>,
    ) -> FxHashSet<Conditioned<Borrow<'tcx>>> {
        self.graph.reborrows_blocked_by(place)
    }

    pub fn reborrows(&self) -> FxHashSet<Conditioned<Borrow<'tcx>>> {
        self.graph.reborrows()
    }

    pub fn bridge(
        &self,
        to: &Self,
        _debug_ctx: DebugCtx,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> BorrowsBridge<'tcx> {
        let added_reborrows: FxHashSet<Conditioned<Borrow<'tcx>>> = to
            .reborrows()
            .into_iter()
            .filter(|rb| !self.has_reborrow_at_location(rb.value.reserve_location()))
            .collect();

        let expands = to
            .deref_expansions()
            .difference(&self.deref_expansions())
            .cloned()
            .collect();

        let mut ug = UnblockGraph::new();

        for reborrow in self.reborrows() {
            if !to.has_reborrow_at_location(reborrow.value.reserve_location()) {
                ug.kill_edge(reborrow.clone().into(), self, repacker);
            }
        }

        for exp in self.deref_expansions().difference(&to.deref_expansions()) {
            ug.kill_edge(exp.clone().into(), self, repacker);
        }

        for abstraction in self.region_abstractions() {
            if !to.region_abstractions().contains(&abstraction) {
                ug.kill_edge(abstraction.clone().into(), self, repacker);
            }
        }

        BorrowsBridge {
            added_borrows: added_reborrows,
            expands,
            ug,
        }
    }

    pub fn ensure_deref_expansions_to_fpcs(
        &mut self,
        tcx: TyCtxt<'tcx>,
        body: &mir::Body<'tcx>,
        summary: &CapabilitySummary<'tcx>,
        location: Location,
    ) {
        for c in (*summary).iter() {
            match c {
                CapabilityLocal::Allocated(projections) => {
                    for (place, kind) in (*projections).iter() {
                        match kind {
                            CapabilityKind::Exclusive => {
                                if place.is_ref(body, tcx) {
                                    self.graph.ensure_deref_expansion_to_at_least(
                                        place.project_deref(PlaceRepacker::new(body, tcx)),
                                        body,
                                        tcx,
                                        location,
                                    );
                                }
                            }
                            _ => {}
                        }
                    }
                }
                _ => {}
            }
        }
    }

    pub fn ensure_expansion_to_exactly(
        &mut self,
        tcx: TyCtxt<'tcx>,
        body: &mir::Body<'tcx>,
        place: Place<'tcx>,
        location: Location,
    ) {
        let mut ug = UnblockGraph::new();
        let repacker = PlaceRepacker::new(body, tcx);
        let graph_edges = self.graph_edges().cloned().collect::<Vec<_>>();
        for p in graph_edges {
            match p.kind() {
                BorrowsEdgeKind::Reborrow(reborrow) => match reborrow.assigned_place {
                    MaybeOldPlace::Current {
                        place: assigned_place,
                    } if place.is_prefix(assigned_place) && !place.is_ref(body, tcx) => {
                        for ra in place.region_projections(repacker) {
                            self.add_region_projection_member(RegionProjectionMember::new(
                                reborrow.blocked_place,
                                ra,
                                location,
                                RegionProjectionMemberDirection::PlaceIsRegionInput,
                            ));
                        }
                    }
                    _ => {}
                },
                _ => {}
            }
        }
        ug.unblock_node(place.into(), self, repacker);
        self.apply_unblock_graph(ug, repacker, location);

        // Originally we may not have been expanded enough
        self.graph
            .ensure_deref_expansion_to_at_least(place.into(), body, tcx, location);
    }

    pub fn roots(&self, repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<MaybeRemotePlace<'tcx>> {
        self.graph.roots(repacker)
    }

    pub fn kill_reborrows(
        &mut self,
        reserve_location: Location,
        kill_location: Location,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        let edges_to_remove = self.reborrow_edges_reserved_at(reserve_location);
        if edges_to_remove.is_empty() {
            return false;
        }
        for edge in edges_to_remove {
            self.remove_edge_and_set_latest(&edge.into(), repacker, kill_location);
        }
        true
    }

    pub fn apply_unblock_graph(
        &mut self,
        graph: UnblockGraph<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
        location: Location,
    ) -> bool {
        let mut changed = false;
        for action in graph.actions(repacker) {
            match action {
                crate::combined_pcs::UnblockAction::TerminateReborrow {
                    reserve_location, ..
                } => {
                    if self.kill_reborrows(reserve_location, location, repacker) {
                        changed = true;
                    }
                }
                crate::combined_pcs::UnblockAction::Collapse(place, _) => {
                    if self.delete_descendants_of(place, repacker, location) {
                        changed = true;
                    }
                }
                crate::combined_pcs::UnblockAction::TerminateAbstraction(location, _call) => {
                    self.graph.remove_abstraction_at(location);
                }
            }
        }
        changed
    }

    pub fn set_latest<T: Into<SnapshotLocation>>(&mut self, place: Place<'tcx>, location: T) {
        self.latest.insert(place, location.into());
    }

    pub fn get_latest(&self, place: Place<'tcx>) -> SnapshotLocation {
        self.latest.get(place)
    }

    pub fn add_region_projection_member(&mut self, member: RegionProjectionMember<'tcx>) {
        self.graph.insert(
            member
                .clone()
                .to_borrows_edge(PathConditions::new(member.location().block)),
        );
    }

    pub fn trim_old_leaves(&mut self, repacker: PlaceRepacker<'_, 'tcx>, location: Location) {
        loop {
            let mut cont = false;
            let edges = self.graph.leaf_edges(repacker);
            for edge in edges {
                if edge.blocked_by_nodes(repacker).iter().all(|p| p.is_old()) {
                    self.remove_edge_and_set_latest(&edge, repacker, location);
                    cont = true;
                }
            }
            if !cont {
                break;
            }
        }
    }

    pub fn add_borrow(
        &mut self,
        blocked_place: MaybeRemotePlace<'tcx>,
        assigned_place: Place<'tcx>,
        mutability: Mutability,
        location: Location,
        region: ty::Region<'tcx>,
    ) {
        self.graph
            .add_borrow(blocked_place, assigned_place, mutability, location, region);
    }

    pub fn has_reborrow_at_location(&self, location: Location) -> bool {
        self.graph.has_reborrow_at_location(location)
    }

    pub fn region_abstractions(&self) -> FxHashSet<Conditioned<AbstractionEdge<'tcx>>> {
        self.graph.abstraction_edges()
    }

    pub fn to_json(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> Value {
        json!({})
    }

    pub fn new() -> Self {
        Self {
            latest: Latest::new(),
            graph: BorrowsGraph::new(),
        }
    }

    pub fn add_region_abstraction(
        &mut self,
        abstraction: AbstractionEdge<'tcx>,
        block: BasicBlock,
    ) {
        self.graph
            .insert(abstraction.to_borrows_edge(PathConditions::new(block)));
    }

    pub fn make_place_old(
        &mut self,
        place: Place<'tcx>,
        _repacker: PlaceRepacker<'_, 'tcx>,
        debug_ctx: Option<DebugCtx>,
    ) {
        self.graph.make_place_old(place, &self.latest, debug_ctx);
    }
}
