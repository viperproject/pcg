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
use crate::{borrow_pcg::action::executed_actions::ExecutedActions, combined_pcs::PcgError};
use crate::{
    borrow_pcg::edge::borrow::{BorrowEdge, LocalBorrow},
    utils::display::DisplayWithRepacker,
};
use crate::{
    borrow_pcg::edge::kind::BorrowPCGEdgeKind, utils::place::maybe_remote::MaybeRemotePlace,
};
use crate::{
    borrow_pcg::edge_data::EdgeData,
    combined_pcs::PCGNode,
    rustc_interface::{
        data_structures::fx::FxHashSet,
        middle::{
            mir::{BasicBlock, BorrowKind, Location, MutBorrowKind},
            ty::{self},
        },
    },
    utils::{display::DebugLines, validity::HasValidityCheck, HasPlace},
    validity_checks_enabled,
};
use crate::{combined_pcs::MaybeHasLocation, utils::place::maybe_old::MaybeOldPlace};
use crate::{
    free_pcs::CapabilityKind,
    utils::{Place, PlaceRepacker, SnapshotLocation},
};
use std::rc::Rc;

pub(crate) mod obtain;

#[derive(Clone, Debug)]
pub struct BorrowsState<'tcx> {
    pub latest: Latest<'tcx>,
    graph: BorrowsGraph<'tcx>,
    pub(crate) capabilities: Rc<BorrowPCGCapabilities<'tcx>>,
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
        }
    }
}

impl<'tcx> BorrowsState<'tcx> {
    pub fn capabilities(&self) -> &BorrowPCGCapabilities<'tcx> {
        self.capabilities.as_ref()
    }
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
                    let _ = self.remove_capability(node.place().into());
                }
            }
        }
        removed
    }

    pub(crate) fn record_and_apply_action(
        &mut self,
        action: BorrowPCGAction<'tcx>,
        actions: &mut ExecutedActions<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Result<(), PcgError> {
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

    pub(crate) fn get_capability(&self, place: MaybeOldPlace<'tcx>) -> Option<CapabilityKind> {
        self.capabilities.get(place)
    }

    /// Returns true iff the capability was changed.
    pub(crate) fn set_capability(
        &mut self,
        place: MaybeOldPlace<'tcx>,
        capability: CapabilityKind,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        assert!(!place.is_owned(repacker));
        if self.get_capability(place) != Some(capability) {
            Rc::<_>::make_mut(&mut self.capabilities).insert(place, capability);
            true
        } else {
            false
        }
    }

    #[must_use]
    pub(crate) fn remove_capability(&mut self, place: MaybeOldPlace<'tcx>) -> bool {
        if self.get_capability(place).is_some() {
            Rc::<_>::make_mut(&mut self.capabilities).remove(place);
            true
        } else {
            false
        }
    }

    pub(crate) fn join<'mir>(
        &mut self,
        other: &Self,
        self_block: BasicBlock,
        other_block: BasicBlock,
        bc: &dyn BorrowCheckerInterface<'mir, 'tcx>,
        repacker: PlaceRepacker<'mir, 'tcx>,
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
    ) -> Result<ExecutedActions<'tcx>, PcgError> {
        tracing::debug!("Removing edge {}", edge.kind().to_short_string(repacker));
        let mut actions = ExecutedActions::new();
        for place in edge.blocked_places(repacker) {
            if let Some(place) = place.as_current_place()
                && self.get_capability(place.into()) != Some(CapabilityKind::Read)
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
            if let Some(place) = node.as_maybe_old_place()
                && !place.is_owned(repacker)
            {
                let blocked_cap = self.get_capability(place);

                let restore_cap = if place.place().projects_shared_ref(repacker) {
                    CapabilityKind::Read
                } else {
                    CapabilityKind::Exclusive
                };

                if blocked_cap.is_none_or(|bc| bc < restore_cap) {
                    self.record_and_apply_action(
                        BorrowPCGAction::restore_capability(place, restore_cap),
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
        bc: &dyn BorrowCheckerInterface<'mir, 'tcx>,
    ) -> Result<ExecutedActions<'tcx>, PcgError> {
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
                bc: &dyn BorrowCheckerInterface<'mir, 'tcx>,
            ) -> Vec<BorrowPCGEdge<'tcx>> {
                let fg = slf.graph.frozen_graph();

                let should_kill_node = |p: LocalNode<'tcx>, fg: &FrozenGraphRef<'slf, 'tcx>| {
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

                let should_pack_edge = |edge: &BorrowPCGEdgeKind<'tcx>| match edge {
                    BorrowPCGEdgeKind::BorrowPCGExpansion(expansion) => {
                        if expansion.expansion().iter().all(|node| {
                            node.is_old()
                                || (prev_location.is_some()
                                    && !bc.is_live(node.place().into(), prev_location.unwrap()))
                        }) {
                            true
                        } else {
                            expansion.expansion().iter().all(|node| {
                                expansion.base().place().is_prefix_exact(node.place())
                                    && expansion.base().location() == node.location()
                            })
                        }
                    }
                    _ => edge
                        .blocked_by_nodes(repacker)
                        .iter()
                        .all(|p| should_kill_node(*p, &fg)),
                };

                let mut edges_to_trim = Vec::new();
                for edge in fg
                    .leaf_edges(repacker)
                    .into_iter()
                    .map(|e| e.to_owned_edge())
                {
                    tracing::debug!(
                        "Checking leaf edge {:?}",
                        edge.kind().to_short_string(repacker)
                    );
                    if should_pack_edge(edge.kind()) {
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
        if !rp.place().is_owned(repacker) {
            self.set_capability(rp.place(), assigned_cap, repacker);
        }
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
                    let _ = self.remove_capability(blocked_place);
                }
                _ => {
                    match self.get_capability(blocked_place) {
                        Some(CapabilityKind::Exclusive) => {
                            assert!(self.set_capability(
                                blocked_place,
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
        self.graph.make_place_old(place, &self.latest, repacker)
    }
}
