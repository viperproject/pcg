use super::{
    action::BorrowPCGAction,
    borrow_pcg_capabilities::BorrowPCGCapabilities,
    borrow_pcg_edge::{
        BlockedNode, BorrowPCGEdge, BorrowPCGEdgeLike, BorrowPCGEdgeRef, LocalNode, ToBorrowsEdge,
    },
    coupling_graph_constructor::BorrowCheckerInterface,
    graph::{BorrowsGraph, FrozenGraphRef},
    latest::Latest,
    path_condition::{PathCondition, PathConditions},
};
use crate::utils::place::maybe_old::MaybeOldPlace;
use crate::utils::place::maybe_remote::MaybeRemotePlace;
use crate::{borrow_pcg::action::executed_actions::ExecutedActions, combined_pcs::PCGError};
use crate::{
    borrow_pcg::edge::borrow::{BorrowEdge, LocalBorrow},
    utils::display::DisplayWithRepacker,
};
use crate::{
    borrow_pcg::edge_data::EdgeData,
    combined_pcs::{PCGNode, PCGNodeLike},
    rustc_interface::{
        data_structures::fx::FxHashSet,
        middle::{
            mir::{BasicBlock, BorrowKind, Location, MutBorrowKind},
            ty::{self},
        },
    },
    utils::{
        display::DebugLines,
        join_lattice_verifier::{HasBlock, JoinLatticeVerifier},
        validity::HasValidityCheck,
        HasPlace,
    },
    validity_checks_enabled,
};
use crate::{
    free_pcs::CapabilityKind,
    utils::{Place, PlaceRepacker, SnapshotLocation},
};
use std::rc::Rc;

pub(crate) mod obtain;

#[cfg(debug_assertions)]
#[derive(Debug, Clone, PartialEq, Eq)]
struct JoinTransitionElem<'tcx> {
    block: BasicBlock,
    latest: Latest<'tcx>,
    graph: BorrowsGraph<'tcx>,
    capabilities: Rc<BorrowPCGCapabilities<'tcx>>,
}

#[cfg(debug_assertions)]
impl HasBlock for JoinTransitionElem<'_> {
    fn block(&self) -> BasicBlock {
        self.block
    }
}

#[cfg(debug_assertions)]
impl<'mir, 'tcx> DebugLines<PlaceRepacker<'mir, 'tcx>> for JoinTransitionElem<'tcx> {
    fn debug_lines(&self, repacker: PlaceRepacker<'mir, 'tcx>) -> Vec<String> {
        let mut lines = Vec::new();
        lines.push(format!("Block: {:?}", self.block));
        for line in self.latest.debug_lines(repacker) {
            lines.push(format!("Latest: {}", line));
        }
        for line in self.graph.debug_lines(repacker) {
            lines.push(format!("Graph: {}", line));
        }
        for line in self.capabilities.debug_lines(repacker) {
            lines.push(format!("Capabilities: {}", line));
        }
        lines
    }
}
/// The "Borrow PCG"
#[derive(Clone, Debug)]
pub struct BorrowsState<'tcx> {
    pub latest: Latest<'tcx>,
    graph: BorrowsGraph<'tcx>,
    pub(crate) capabilities: Rc<BorrowPCGCapabilities<'tcx>>,
    #[cfg(debug_assertions)]
    #[allow(dead_code)]
    join_transitions: JoinLatticeVerifier<JoinTransitionElem<'tcx>>,
}

impl<'tcx> DebugLines<PlaceRepacker<'_, 'tcx>> for BorrowsState<'tcx> {
    fn debug_lines(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Vec<String> {
        let mut lines = Vec::new();
        lines.extend(self.graph.debug_lines(repacker));
        lines.extend(self.capabilities.debug_lines(repacker));
        lines
    }
}

impl Eq for BorrowsState<'_> {}

impl PartialEq for BorrowsState<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.latest == other.latest
            && self.graph == other.graph
            && self.capabilities == other.capabilities
    }
}

impl<'tcx> HasValidityCheck<'tcx> for BorrowsState<'tcx> {
    fn check_validity(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Result<(), String> {
        self.graph.check_validity(repacker)
    }
}

impl Default for BorrowsState<'_> {
    fn default() -> Self {
        Self {
            latest: Latest::new(),
            graph: BorrowsGraph::new(),
            capabilities: Rc::new(BorrowPCGCapabilities::new()),
            #[cfg(debug_assertions)]
            join_transitions: JoinLatticeVerifier::new(),
        }
    }
}

impl<'tcx> BorrowsState<'tcx> {
    pub(crate) fn insert(&mut self, edge: BorrowPCGEdge<'tcx>) -> bool {
        self.graph.insert(edge)
    }
    pub(super) fn remove(
        &mut self,
        edge: &BorrowPCGEdge<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        let removed = self.graph.remove(edge);
        if removed {
            for node in edge.blocked_by_nodes(repacker) {
                if !self.graph.contains(node, repacker) {
                    let _ = self.remove_capability(node.into());
                }
            }
        }
        removed
    }

    fn record_and_apply_action(
        &mut self,
        action: BorrowPCGAction<'tcx>,
        actions: &mut ExecutedActions<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Result<(), PCGError> {
        let changed = self.apply_action(action.clone(), repacker)?;
        if changed {
            actions.record(action);
        }
        Ok(())
    }

    pub(crate) fn contains<T: Into<PCGNode<'tcx>>>(
        &self,
        node: T,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        self.graph.contains(node.into(), repacker)
    }

    pub(crate) fn graph_edges<'slf>(
        &'slf self,
    ) -> impl Iterator<Item = BorrowPCGEdgeRef<'tcx, 'slf>> {
        self.graph.edges()
    }

    pub fn graph(&self) -> &BorrowsGraph<'tcx> {
        &self.graph
    }

    pub(crate) fn frozen_graph(&self) -> FrozenGraphRef<'_, 'tcx> {
        self.graph().frozen_graph()
    }

    pub(crate) fn get_capability(&self, node: PCGNode<'tcx>) -> Option<CapabilityKind> {
        self.capabilities.get(node)
    }

    /// Returns true iff the capability was changed.
    pub(crate) fn set_capability(
        &mut self,
        node: PCGNode<'tcx>,
        capability: CapabilityKind,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        assert!(!node.is_owned(repacker));
        if self.get_capability(node) != Some(capability) {
            Rc::<_>::make_mut(&mut self.capabilities).insert(node, capability);
            true
        } else {
            false
        }
    }

    #[must_use]
    pub(crate) fn remove_capability(&mut self, node: PCGNode<'tcx>) -> bool {
        if self.get_capability(node).is_some() {
            Rc::<_>::make_mut(&mut self.capabilities).remove(node);
            true
        } else {
            false
        }
    }

    #[cfg(debug_assertions)]
    #[allow(dead_code)]
    fn join_transition_elem(self, block: BasicBlock) -> JoinTransitionElem<'tcx> {
        JoinTransitionElem {
            block,
            latest: self.latest,
            graph: self.graph,
            capabilities: self.capabilities,
        }
    }

    pub(crate) fn join<'mir, T: BorrowCheckerInterface<'tcx>>(
        &mut self,
        other: &Self,
        self_block: BasicBlock,
        other_block: BasicBlock,
        bc: &T,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        let mut changed = false;
        changed |= self
            .graph
            .join(&other.graph, self_block, other_block, repacker, bc);
        changed |= self.latest.join(&other.latest, self_block, repacker);
        if other.capabilities != self.capabilities {
            changed |= Rc::<_>::make_mut(&mut self.capabilities).join(&other.capabilities);
        }
        changed
    }

    #[must_use]
    pub(crate) fn rename_place(
        &mut self,
        old: MaybeOldPlace<'tcx>,
        new: MaybeOldPlace<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        let mut changed = self.graph.rename_place(old, new, repacker);
        changed |= Rc::<_>::make_mut(&mut self.capabilities).rename_place(old, new);
        changed
    }

    pub(super) fn remove_edge_and_set_latest(
        &mut self,
        edge: impl BorrowPCGEdgeLike<'tcx>,
        location: Location,
        repacker: PlaceRepacker<'_, 'tcx>,
        context: &str,
    ) -> Result<ExecutedActions<'tcx>, PCGError> {
        tracing::debug!("Removing edge {}", edge.kind().to_short_string(repacker));
        let mut actions = ExecutedActions::new();
        for place in edge.blocked_places(repacker) {
            if self.get_capability(place.into()) != Some(CapabilityKind::Read)
                && let Some(place) = place.as_current_place()
                && place.has_location_dependent_value(repacker)
            {
                self.record_and_apply_action(
                    BorrowPCGAction::set_latest(place, location, context),
                    &mut actions,
                    repacker,
                )?;
            }
        }
        let remove_edge_action =
            BorrowPCGAction::remove_edge(edge.clone().to_owned_edge(), context);
        self.record_and_apply_action(remove_edge_action, &mut actions, repacker)?;

        let fg = self.graph().frozen_graph();
        let to_restore = edge
            .blocked_nodes(repacker)
            .into_iter()
            .filter(|node| !fg.has_edge_blocking(*node, repacker))
            .collect::<Vec<_>>();
        for node in to_restore {
            if let Some(local_node) = node.as_local_node(repacker) {
                let blocked_cap = self.get_capability(node);

                let restore_cap = if local_node.place().projects_shared_ref(repacker) {
                    CapabilityKind::Read
                } else {
                    CapabilityKind::Exclusive
                };

                if blocked_cap.is_none_or(|bc| bc < restore_cap) {
                    self.record_and_apply_action(
                        BorrowPCGAction::restore_capability(local_node, restore_cap),
                        &mut actions,
                        repacker,
                    )?;
                }
            }
        }
        Ok(actions)
    }

    pub(crate) fn add_path_condition(&mut self, pc: PathCondition) -> bool {
        self.graph.add_path_condition(pc)
    }

    pub fn filter_for_path(&mut self, path: &[BasicBlock]) {
        self.graph.filter_for_path(path);
    }

    /// Returns the place that blocks `place` if:
    /// 1. there is exactly one hyperedge blocking `place`
    /// 2. that edge is blocked by exactly one node
    /// 3. that node is a region projection that can be dereferenced
    ///
    /// This is used in the symbolic-execution based purification encoding to
    /// compute the backwards function for the argument local `place`. It
    /// depends on `Borrow` edges connecting the remote input to a single node
    /// in the PCG. In the symbolic execution, backward function results are computed
    /// per-path, so this expectation may be reasonable in that context.
    pub fn get_place_blocking(
        &self,
        place: MaybeRemotePlace<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Option<MaybeOldPlace<'tcx>> {
        let edges = self.edges_blocking(place.into(), repacker);
        if edges.len() != 1 {
            return None;
        }
        let nodes = edges[0].blocked_by_nodes(repacker);
        if nodes.len() != 1 {
            return None;
        }
        let node = nodes.into_iter().next().unwrap();
        match node {
            PCGNode::Place(_) => todo!(),
            PCGNode::RegionProjection(region_projection) => region_projection.deref(repacker),
        }
    }

    pub(crate) fn edges_blocking<'slf, 'mir: 'slf>(
        &'slf self,
        node: BlockedNode<'tcx>,
        repacker: PlaceRepacker<'mir, 'tcx>,
    ) -> Vec<BorrowPCGEdgeRef<'tcx, 'slf>> {
        self.graph.edges_blocking(node, repacker).collect()
    }

    pub(crate) fn roots(&self, repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<PCGNode<'tcx>> {
        self.graph.roots(repacker)
    }

    pub(crate) fn get_latest(&self, place: Place<'tcx>) -> SnapshotLocation {
        self.latest.get(place)
    }

    /// Removes leaves that are old or dead (based on the borrow checker). Note
    /// that the liveness calculation is performed based on what happened at the
    /// end of the *previous* statement.
    ///
    /// For example when evaluating:
    /// ```text
    /// bb0[1]: let x = &mut y;
    /// bb0[2]: *x = 2;
    /// bb0[3]: ... // x is dead
    /// ```
    /// would not remove the *x -> y edge until this function is called at `bb0[3]`.
    /// This ensures that the edge appears in the graph at the end of `bb0[2]`
    /// (rather than never at all).
    ///
    /// Additional caveat: we do not remove dead places that are function
    /// arguments. At least for now this interferes with the implementation in
    /// the Prusti purified encoding for accessing the final value of a
    /// reference-typed function argument in its postcondition.
    pub(super) fn pack_old_and_dead_leaves<'slf, 'mir>(
        &'slf mut self,
        repacker: PlaceRepacker<'mir, 'tcx>,
        location: Location,
        bc: &impl BorrowCheckerInterface<'tcx>,
    ) -> Result<ExecutedActions<'tcx>, PCGError> {
        let mut actions = ExecutedActions::new();
        let prev_location = if location.statement_index == 0 {
            None
        } else {
            Some(Location {
                block: location.block,
                statement_index: location.statement_index - 1,
            })
        };
        let mut num_edges_prev = self.graph.num_edges();
        loop {
            fn go<'slf, 'mir, 'tcx>(
                slf: &'slf mut BorrowsState<'tcx>,
                repacker: PlaceRepacker<'mir, 'tcx>,
                prev_location: Option<Location>,
                bc: &impl BorrowCheckerInterface<'tcx>,
            ) -> Vec<BorrowPCGEdge<'tcx>> {
                let fg = slf.graph.frozen_graph();
                let should_trim = |p: LocalNode<'tcx>, fg: &FrozenGraphRef<'slf, 'tcx>| {
                    if p.is_old() {
                        return true;
                    }
                    let place = match p {
                        PCGNode::Place(p) => p.place(),
                        PCGNode::RegionProjection(rp) => rp.place().place(),
                    };

                    if place.projection.is_empty() && repacker.is_arg(place.local) {
                        return false;
                    }

                    if !place.projection.is_empty() && !fg.has_edge_blocking(place.into(), repacker)
                    {
                        return true;
                    }

                    prev_location.is_some() && !bc.is_live(place.into(), prev_location.unwrap())
                };

                let mut edges_to_trim = Vec::new();
                for edge in fg
                    .leaf_edges(repacker)
                    .into_iter()
                    .map(|e| e.to_owned_edge())
                {
                    let blocked_by_nodes = edge.blocked_by_nodes(repacker);
                    if blocked_by_nodes.iter().all(|p| should_trim(*p, &fg)) {
                        edges_to_trim.push(edge);
                    }
                }
                edges_to_trim
            }
            let edges_to_trim = go(self, repacker, prev_location, bc);
            if edges_to_trim.is_empty() {
                break Ok(actions);
            }
            for edge in edges_to_trim {
                actions.extend(self.remove_edge_and_set_latest(
                    edge,
                    location,
                    repacker,
                    "Trim Old Leaves",
                )?);
            }
            let new_num_edges = self.graph.num_edges();
            assert!(new_num_edges < num_edges_prev);
            num_edges_prev = new_num_edges;
        }
    }

    pub(crate) fn add_borrow(
        &mut self,
        blocked_place: MaybeOldPlace<'tcx>,
        assigned_place: Place<'tcx>,
        kind: BorrowKind,
        location: Location,
        region: ty::Region<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) {
        assert!(
            assigned_place.ty(repacker).ty.ref_mutability().is_some(),
            "{:?}:{:?} Assigned place {:?} is not a reference. Ty: {:?}",
            repacker.body().source.def_id(),
            location,
            assigned_place,
            assigned_place.ty(repacker).ty
        );
        let assigned_cap = match kind {
            BorrowKind::Mut {
                kind: MutBorrowKind::Default,
            } => CapabilityKind::Exclusive,
            _ => CapabilityKind::Read,
        };
        let borrow_edge = LocalBorrow::new(
            blocked_place,
            assigned_place.into(),
            kind,
            location,
            region,
            repacker,
        );
        let rp = borrow_edge.assigned_region_projection(repacker);
        self.set_capability(rp.to_pcg_node(repacker), assigned_cap, repacker);
        assert!(self.graph.insert(
            BorrowEdge::Local(borrow_edge)
                .to_borrow_pcg_edge(PathConditions::AtBlock(location.block))
        ));

        // Update the capability of the blocked place, if necessary
        if !blocked_place.is_owned(repacker) {
            match kind {
                BorrowKind::Mut {
                    kind: MutBorrowKind::Default,
                } => {
                    let _ = self.remove_capability(blocked_place.into());
                }
                _ => {
                    match self.get_capability(blocked_place.into()) {
                        Some(CapabilityKind::Exclusive) => {
                            assert!(self.set_capability(
                                blocked_place.into(),
                                CapabilityKind::Read,
                                repacker
                            ));
                        }
                        Some(CapabilityKind::Read) => {
                            // Do nothing, this just adds another shared borrow
                        }
                        None => {
                            // Some projections are currently incomplete (e.g. ConstantIndex)
                            // therefore we don't expect a capability here. For more information
                            // see the comment in `Place::expand_one_level`.
                            // TODO: Make such projections complete
                        }
                        other => {
                            if validity_checks_enabled() {
                                unreachable!(
                                    "{:?}: Unexpected capability for borrow blocked place {:?}: {:?}",
                                    location, blocked_place, other
                                );
                            }
                        }
                    }
                }
            };
        }
    }

    #[must_use]
    pub(crate) fn make_place_old(
        &mut self,
        place: Place<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        let mut changed = self.graph.make_place_old(place, &self.latest, repacker);
        changed |=
            Rc::<_>::make_mut(&mut self.capabilities).make_place_old(place, &self.latest, repacker);
        changed
    }
}
