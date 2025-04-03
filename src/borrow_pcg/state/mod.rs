use super::{
    action::BorrowPCGAction,
    borrow_pcg_edge::{
        BlockedNode, BorrowPCGEdge, BorrowPCGEdgeLike, BorrowPCGEdgeRef, LocalNode, ToBorrowsEdge,
    },
    coupling_graph_constructor::BorrowCheckerInterface,
    edge::borrow::RemoteBorrow,
    graph::{frozen::FrozenGraphRef, BorrowsGraph},
    has_pcs_elem::LabelRegionProjection,
    latest::Latest,
    path_condition::{PathCondition, PathConditions},
    visitor::extract_regions,
};
use crate::{
    borrow_pcg::edge::kind::BorrowPCGEdgeKind, utils::place::maybe_remote::MaybeRemotePlace,
};
use crate::{
    borrow_pcg::edge::{
        borrow::{BorrowEdge, LocalBorrow},
        outlives::OutlivesEdgeKind,
    },
    pcg::place_capabilities::PlaceCapabilities,
};
use crate::{
    borrow_pcg::edge_data::EdgeData,
    pcg::PCGNode,
    rustc_interface::{
        data_structures::fx::FxHashSet,
        middle::{
            mir::{self, BasicBlock, BorrowKind, Location, MutBorrowKind},
            ty::{self},
        },
    },
    utils::{display::DebugLines, validity::HasValidityCheck, HasPlace},
    validity_checks_enabled,
};
use crate::{
    borrow_pcg::{
        action::executed_actions::ExecutedActions, edge::outlives::OutlivesEdge,
        region_projection::RegionProjection,
    },
    pcg::PcgError,
    utils::remote::RemotePlace,
};
use crate::{
    free_pcs::CapabilityKind,
    utils::{Place, PlaceRepacker, SnapshotLocation},
};
use crate::{pcg::MaybeHasLocation, utils::place::maybe_old::MaybeOldPlace};

pub(crate) mod obtain;

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct BorrowsState<'tcx> {
    pub latest: Latest<'tcx>,
    graph: BorrowsGraph<'tcx>,
}

impl<'tcx> DebugLines<PlaceRepacker<'_, 'tcx>> for BorrowsState<'tcx> {
    fn debug_lines(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Vec<String> {
        let mut lines = Vec::new();
        lines.extend(self.graph.debug_lines(repacker));
        lines
    }
}

impl<'tcx> HasValidityCheck<'tcx> for BorrowsState<'tcx> {
    fn check_validity(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Result<(), String> {
        self.graph.check_validity(repacker)
    }
}

impl<'tcx> BorrowsState<'tcx> {
    pub(crate) fn label_region_projection(
        &mut self,
        projection: &RegionProjection<'tcx, MaybeOldPlace<'tcx>>,
        location: SnapshotLocation,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) {
        self.graph
            .mut_edges(|edge| edge.label_region_projection(projection, location, repacker));
    }
    fn introduce_initial_borrows(
        &mut self,
        local: mir::Local,
        capabilities: &mut PlaceCapabilities<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) {
        let local_decl = &repacker.body().local_decls[local];
        let arg_place: Place<'tcx> = local.into();
        if let ty::TyKind::Ref(_, _, _) = local_decl.ty.kind() {
            let _ = self.apply_action(
                BorrowPCGAction::add_edge(RemoteBorrow::new(local).into(), true),
                capabilities,
                repacker,
            );
        }
        for region in extract_regions(local_decl.ty, repacker) {
            let region_projection =
                RegionProjection::new(region, arg_place.into(), None, repacker).unwrap();
            assert!(self
                .apply_action(
                    BorrowPCGAction::add_edge(
                        BorrowPCGEdge::new(
                            OutlivesEdge::new(
                                RegionProjection::new(
                                    region,
                                    RemotePlace::new(local).into(),
                                    None,
                                    repacker,
                                )
                                .unwrap_or_else(|e| {
                                    panic!(
                                        "Failed to create region for remote place (for {local:?}).
                                    Local ty: {:?}. Error: {:?}",
                                        local_decl.ty, e
                                    );
                                }),
                                region_projection,
                                OutlivesEdgeKind::InitialBorrows,
                                repacker,
                            )
                            .into(),
                            PathConditions::AtBlock((Location::START).block),
                        ),
                        true,
                    ),
                    capabilities,
                    repacker,
                )
                .unwrap());
        }
    }

    pub(crate) fn initialize_as_start_block(
        &mut self,
        capabilities: &mut PlaceCapabilities<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) {
        for arg in repacker.body().args_iter() {
            self.introduce_initial_borrows(arg, capabilities, repacker);
        }
    }

    pub(crate) fn insert(&mut self, edge: BorrowPCGEdge<'tcx>) -> bool {
        self.graph.insert(edge)
    }

    pub(super) fn remove(
        &mut self,
        edge: &BorrowPCGEdge<'tcx>,
        capabilities: &mut PlaceCapabilities<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        let removed = self.graph.remove(edge);
        if removed {
            for node in edge.blocked_by_nodes(repacker) {
                if !self.graph.contains(node, repacker) {
                    if let PCGNode::Place(MaybeOldPlace::Current { place }) = node {
                        let _ = capabilities.remove(place.into());
                    }
                }
            }
        }
        removed
    }

    pub(crate) fn record_and_apply_action(
        &mut self,
        action: BorrowPCGAction<'tcx>,
        actions: &mut ExecutedActions<'tcx>,
        capabilities: &mut PlaceCapabilities<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Result<(), PcgError> {
        let changed = self.apply_action(action.clone(), capabilities, repacker)?;
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

    pub fn graph(&self) -> &BorrowsGraph<'tcx> {
        &self.graph
    }

    pub(crate) fn frozen_graph(&self) -> FrozenGraphRef<'_, 'tcx> {
        self.graph().frozen_graph()
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
        changed |= self.latest.join(&other.latest, self_block);
        changed
    }

    #[tracing::instrument(skip(self, edge, location, repacker))]
    pub(super) fn remove_edge_and_set_latest(
        &mut self,
        edge: impl BorrowPCGEdgeLike<'tcx>,
        capabilities: &mut PlaceCapabilities<'tcx>,
        location: Location,
        repacker: PlaceRepacker<'_, 'tcx>,
        context: &str,
    ) -> Result<ExecutedActions<'tcx>, PcgError> {
        let mut actions = ExecutedActions::new();
        for place in edge.blocked_places(repacker) {
            if let Some(place) = place.as_current_place()
                && capabilities.get(place.into()) != Some(CapabilityKind::Read)
                && place.has_location_dependent_value(repacker)
            {
                self.record_and_apply_action(
                    BorrowPCGAction::set_latest(place, location, context),
                    &mut actions,
                    capabilities,
                    repacker,
                )?;
            }
        }
        let remove_edge_action =
            BorrowPCGAction::remove_edge(edge.clone().to_owned_edge(), context);
        self.record_and_apply_action(remove_edge_action, &mut actions, capabilities, repacker)?;

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
                let blocked_cap = capabilities.get(place);

                let restore_cap = if place.place().projects_shared_ref(repacker) {
                    CapabilityKind::Read
                } else {
                    CapabilityKind::Exclusive
                };

                if blocked_cap.is_none_or(|bc| bc < restore_cap) {
                    self.record_and_apply_action(
                        BorrowPCGAction::restore_capability(place, restore_cap),
                        &mut actions,
                        capabilities,
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

    /// Removes leaves that are old or dead (based on the borrow checker). This
    /// function should called prior to evaluating the effect of the statement
    /// at `location`.
    ///
    /// Note that the liveness calculation is performed based on what happened
    /// at the end of the *previous* statement.
    ///
    /// For example when evaluating:
    /// ```text
    /// bb0[1]: let x = &mut y;
    /// bb0[2]: *x = 2;
    /// bb0[3]: ... // x is dead
    /// ```
    /// we do not remove the `*x -> y` edge until `bb0[3]`.
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
        capabilities: &mut PlaceCapabilities<'tcx>,
        location: Location,
        bc: &dyn BorrowCheckerInterface<'mir, 'tcx>,
    ) -> Result<ExecutedActions<'tcx>, PcgError> {
        let mut actions = ExecutedActions::new();
        let mut num_edges_prev = self.graph.num_edges();
        loop {
            fn go<'slf, 'mir: 'slf, 'tcx>(
                slf: &'slf mut BorrowsState<'tcx>,
                repacker: PlaceRepacker<'mir, 'tcx>,
                location: Location,
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

                    bc.is_dead(place.into(), location)
                };

                let should_pack_edge =
                    |edge: &BorrowPCGEdgeKind<'tcx>| match edge {
                        BorrowPCGEdgeKind::BorrowPCGExpansion(expansion) => {
                            if expansion.expansion().iter().all(|node| {
                                node.is_old() || bc.is_dead(node.place().into(), location)
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
                    if should_pack_edge(edge.kind()) {
                        edges_to_trim.push(edge);
                    }
                }
                edges_to_trim
            }
            let edges_to_trim = go(self, repacker, location, bc);
            if edges_to_trim.is_empty() {
                break Ok(actions);
            }
            for edge in edges_to_trim {
                actions.extend(self.remove_edge_and_set_latest(
                    edge,
                    capabilities,
                    location,
                    repacker,
                    "Trim Old Leaves",
                )?);
            }
            let new_num_edges = self.graph.num_edges();
            assert!(new_num_edges <= num_edges_prev);
            num_edges_prev = new_num_edges;
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn add_borrow(
        &mut self,
        blocked_place: MaybeOldPlace<'tcx>,
        assigned_place: Place<'tcx>,
        kind: BorrowKind,
        location: Location,
        region: ty::Region<'tcx>,
        capabilities: &mut PlaceCapabilities<'tcx>,
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
        capabilities.insert(rp.place(), assigned_cap);
        assert!(self.graph.insert(
            BorrowEdge::Local(borrow_edge)
                .to_borrow_pcg_edge(PathConditions::AtBlock(location.block))
        ));

        match kind {
            BorrowKind::Mut {
                kind: MutBorrowKind::Default,
            } => {
                let _ = capabilities.remove(blocked_place);
            }
            _ => {
                match capabilities.get(blocked_place) {
                    Some(CapabilityKind::Exclusive) => {
                        assert!(capabilities.insert(blocked_place, CapabilityKind::Read,));
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
