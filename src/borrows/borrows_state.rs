use tracing::instrument;

use crate::{
    borrows::edge_data::EdgeData,
    rustc_interface::{
        ast::Mutability,
        data_structures::fx::FxHashSet,
        middle::{
            mir::{BasicBlock, Location},
            ty::{self},
        },
    },
    utils::{HasPlace, ProjectionKind},
    RestoreCapability,
};

use crate::{
    free_pcs::CapabilityKind,
    utils::{Place, PlaceRepacker, SnapshotLocation},
    BorrowsBridge, Weaken,
};

use super::{
    borrow_edge::BorrowEdge,
    borrow_pcg_action::BorrowPCGAction,
    borrow_pcg_capabilities::BorrowPCGCapabilities,
    borrow_pcg_edge::{
        BlockedNode, BorrowPCGEdge, BorrowPCGEdgeKind, LocalNode, PCGNode, ToBorrowsEdge,
    },
    borrow_pcg_expansion::{BorrowExpansion, BorrowPCGExpansion, ExpansionOfOwned},
    borrows_graph::{BorrowsGraph, Conditioned},
    borrows_visitor::DebugCtx,
    coupling_graph_constructor::{BorrowCheckerInterface, CGNode, Coupled},
    domain::{AbstractionType, MaybeOldPlace, MaybeRemotePlace},
    has_pcs_elem::HasPcsElems,
    latest::Latest,
    path_condition::{PathCondition, PathConditions},
    region_abstraction::AbstractionEdge,
    region_projection::RegionProjection,
    region_projection_member::RegionProjectionMember,
    unblock_graph::{BorrowPCGUnblockAction, UnblockGraph, UnblockType},
};

#[derive(Debug)]
pub(crate) struct ExecutedActions<'tcx> {
    actions: Vec<BorrowPCGAction<'tcx>>,
    changed: bool,
}

impl<'tcx> ExecutedActions<'tcx> {
    fn new() -> Self {
        Self {
            actions: vec![],
            changed: false,
        }
    }

    pub(crate) fn changed(&self) -> bool {
        self.changed
    }

    fn record(&mut self, action: BorrowPCGAction<'tcx>, changed: bool) {
        self.actions.push(action);
        self.changed |= changed;
    }

    fn extend(&mut self, actions: ExecutedActions<'tcx>) {
        self.actions.extend(actions.actions);
        self.changed |= actions.changed;
    }

    pub(super) fn actions(self) -> Vec<BorrowPCGAction<'tcx>> {
        self.actions
    }
}

/// The "Borrow PCG"
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BorrowsState<'tcx> {
    pub latest: Latest<'tcx>,
    graph: BorrowsGraph<'tcx>,
    capabilities: BorrowPCGCapabilities<'tcx>,
}

impl<'tcx> Default for BorrowsState<'tcx> {
    fn default() -> Self {
        Self {
            latest: Latest::new(),
            graph: BorrowsGraph::new(),
            capabilities: BorrowPCGCapabilities::new(),
        }
    }
}

impl<'tcx> BorrowsState<'tcx> {
    pub(crate) fn debug_capability_lines(&self) -> Vec<String> {
        self.capabilities.debug_capability_lines()
    }
    pub(crate) fn insert(&mut self, edge: BorrowPCGEdge<'tcx>) -> bool {
        self.graph.insert(edge)
    }
    pub(super) fn remove(&mut self, edge: &BorrowPCGEdge<'tcx>) -> bool {
        self.graph.remove(edge)
    }
    pub(crate) fn is_valid(&self, repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        self.graph.is_valid(repacker)
    }

    fn record_and_apply_action(
        &mut self,
        action: BorrowPCGAction<'tcx>,
        actions: &mut ExecutedActions<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) {
        let changed = self.apply_action(action.clone(), repacker);
        actions.record(action, changed);
    }

    pub(crate) fn place_capabilities(
        &self,
    ) -> impl Iterator<Item = (Place<'tcx>, CapabilityKind)> + '_ {
        self.capabilities.place_capabilities()
    }

    pub(crate) fn contains<T: Into<PCGNode<'tcx>>>(
        &self,
        node: T,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        self.graph.contains(node.into(), repacker)
    }
    pub fn capabilities(&self) -> &BorrowPCGCapabilities<'tcx> {
        &self.capabilities
    }

    pub fn graph_edges(&self) -> impl Iterator<Item = &BorrowPCGEdge<'tcx>> {
        self.graph.edges()
    }

    pub fn graph(&self) -> &BorrowsGraph<'tcx> {
        &self.graph
    }

    pub fn get_capability<T: Into<PCGNode<'tcx>>>(&self, node: T) -> Option<CapabilityKind> {
        self.capabilities.get(node.into())
    }

    /// Returns true iff the capability was changed.
    pub(crate) fn set_capability<T: Into<PCGNode<'tcx>> + std::fmt::Debug>(
        &mut self,
        node: T,
        capability: CapabilityKind,
    ) -> bool {
        self.capabilities.insert(node, capability)
    }

    pub(crate) fn remove_capability<T: Into<PCGNode<'tcx>> + std::fmt::Debug>(
        &mut self,
        node: T,
    ) -> bool {
        self.capabilities.remove(node)
    }

    pub(crate) fn join<'mir, T: BorrowCheckerInterface<'tcx>>(
        &mut self,
        other: &Self,
        self_block: BasicBlock,
        other_block: BasicBlock,
        bc: &T,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        if repacker.should_check_validity() {
            debug_assert!(other.graph.is_valid(repacker), "Other graph is invalid");
        }
        let mut changed = false;
        if self
            .graph
            .join(&other.graph, self_block, other_block, repacker, bc)
        {
            changed = true;
        }
        if self.latest.join(&other.latest, self_block, repacker) {
            // TODO: Setting changed to true prevents divergence for loops,
            // think about how latest should work in loops

            // changed = true;
        }
        if self.capabilities.join(&other.capabilities) {
            changed = true;
        }
        changed
    }

    #[must_use]
    pub(crate) fn change_pcs_elem<T: 'tcx>(&mut self, old: T, new: T) -> bool
    where
        T: PartialEq + Clone,
        BorrowPCGEdge<'tcx>: HasPcsElems<T>,
    {
        self.graph.change_pcs_elem(old, new)
    }

    #[must_use]
    pub(super) fn remove_edge_and_set_latest(
        &mut self,
        edge: &BorrowPCGEdge<'tcx>,
        location: Location,
        repacker: PlaceRepacker<'_, 'tcx>,
        context: &str,
    ) -> ExecutedActions<'tcx> {
        let mut actions = ExecutedActions::new();
        if !edge.is_shared_borrow() {
            for place in edge.blocked_places(repacker) {
                if let Some(place) = place.as_current_place() {
                    if place.has_location_dependent_value(repacker) {
                        self.record_and_apply_action(
                            BorrowPCGAction::set_latest(place, location, context),
                            &mut actions,
                            repacker,
                        );
                    }
                }
            }
        }
        let remove_edge_action = BorrowPCGAction::remove_edge(edge.clone(), context);
        let result = self.apply_action(remove_edge_action.clone(), repacker);
        actions.record(remove_edge_action, result);
        // If removing the edge results in a leaf node with a Lent capability, this
        // it should be set to Exclusive, as it is no longer being lent.
        if result {
            for node in self.graph.leaf_nodes(repacker) {
                if self.get_capability(node) == Some(CapabilityKind::Lent) {
                    self.set_capability(node, CapabilityKind::Exclusive);
                }
            }
        }
        actions
    }

    /// Collapses nodes using the following rules:
    /// - If a node is only blocked by old leaves, then its expansion should be collapsed
    /// - If a borrow PCG node's expansion is only leaves, then its expansion should be collapsed
    ///
    /// This function performs such collapses until a fixpoint is reached
    #[must_use]
    pub(crate) fn minimize(
        &mut self,
        repacker: PlaceRepacker<'_, 'tcx>,
        location: Location,
    ) -> ExecutedActions<'tcx> {
        let mut actions = ExecutedActions::new();
        loop {
            let edges = self.graph.edges().cloned().collect::<Vec<_>>();
            let num_edges_prev = edges.len();
            let to_remove = edges
                .into_iter()
                .filter(|edge| {
                    let is_old_unblocked = edge
                        .blocked_by_nodes(repacker)
                        .iter()
                        .all(|p| p.is_old() && !self.graph.has_edge_blocking(*p, repacker));
                    let is_borrow_pcg_expansion = match &edge.kind() {
                        BorrowPCGEdgeKind::BorrowPCGExpansion(de) => {
                            !de.is_owned_expansion()
                                && de
                                    .expansion(repacker)
                                    .into_iter()
                                    .all(|p| !self.graph.has_edge_blocking(p, repacker))
                        }
                        _ => false,
                    };
                    is_old_unblocked || is_borrow_pcg_expansion
                })
                .collect::<Vec<_>>();
            if to_remove.is_empty() {
                break actions;
            }
            for edge in to_remove {
                actions
                    .extend(self.remove_edge_and_set_latest(&edge, location, repacker, "Minimize"));
            }
            assert!(self.graph.edge_count() < num_edges_prev);
        }
    }

    pub(crate) fn add_path_condition(&mut self, pc: PathCondition) -> bool {
        self.graph.add_path_condition(pc)
    }

    pub fn filter_for_path(&mut self, path: &[BasicBlock]) {
        self.graph.filter_for_path(path);
    }

    pub(crate) fn borrows_blocking_prefix_of(
        &self,
        place: Place<'tcx>,
    ) -> FxHashSet<Conditioned<BorrowEdge<'tcx>>> {
        self.borrows()
            .into_iter()
            .filter(|rb| match rb.value.blocked_place {
                MaybeRemotePlace::Local(MaybeOldPlace::Current {
                    place: blocked_place,
                }) => blocked_place.is_prefix(place),
                _ => false,
            })
            .collect()
    }

    #[must_use]
    pub(crate) fn delete_descendants_of(
        &mut self,
        place: MaybeOldPlace<'tcx>,
        location: Location,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> ExecutedActions<'tcx> {
        let mut actions = ExecutedActions::new();
        let edges = self.edges_blocking(place.into(), repacker);
        if edges.is_empty() {
            return actions;
        }
        for edge in edges {
            actions.extend(self.remove_edge_and_set_latest(
                &edge,
                location,
                repacker,
                "Delete Descendants",
            ));
        }
        actions
    }

    /// Returns the place that blocks `place` if:
    /// 1. there is exactly one edge blocking `place`
    /// 2. that edge is a borrow edge
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
        match edges[0].kind() {
            BorrowPCGEdgeKind::Borrow(reborrow) => Some(reborrow.deref_place(repacker)),
            BorrowPCGEdgeKind::BorrowPCGExpansion(_) => todo!(),
            BorrowPCGEdgeKind::Abstraction(_) => todo!(),
            BorrowPCGEdgeKind::RegionProjectionMember(_) => None,
        }
    }

    pub(crate) fn edges_blocking(
        &self,
        node: BlockedNode<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Vec<BorrowPCGEdge<'tcx>> {
        self.graph.edges_blocking(node, repacker)
    }

    pub(crate) fn edges_blocked_by(
        &self,
        node: LocalNode<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> FxHashSet<BorrowPCGEdge<'tcx>> {
        self.graph.edges_blocked_by(node, repacker)
    }

    pub(crate) fn borrow_pcg_expansions(&self) -> FxHashSet<Conditioned<BorrowPCGExpansion<'tcx>>> {
        self.graph.borrow_pcg_expansions()
    }

    pub(crate) fn borrows(&self) -> FxHashSet<Conditioned<BorrowEdge<'tcx>>> {
        self.graph.borrows()
    }

    pub(crate) fn bridge(
        &self,
        to: &Self,
        _debug_ctx: DebugCtx,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> BorrowsBridge<'tcx> {
        let added_borrows: FxHashSet<Conditioned<BorrowEdge<'tcx>>> = to
            .borrows()
            .into_iter()
            .filter(|rb| !self.has_borrow_at_location(rb.value.reserve_location()))
            .collect();

        let expands = to
            .borrow_pcg_expansions()
            .difference(&self.borrow_pcg_expansions())
            .cloned()
            .collect();

        let added_region_projection_members = to
            .graph
            .region_projection_members()
            .difference(&self.graph.region_projection_members())
            .cloned()
            .collect();

        let mut ug = UnblockGraph::new();

        for borrow in self.borrows() {
            if !to.has_borrow_at_location(borrow.value.reserve_location()) {
                ug.kill_edge(
                    borrow.clone().into(),
                    self,
                    repacker,
                    UnblockType::ForExclusive,
                );
            }
        }

        // Two nodes are conceptually the same place if:
        // 1) they are actually equal
        // 2) if `self_place` is a current place and `to_place` is a snapshotted
        // version of that same place which is current w.r.t `self`
        //
        // TODO: Confirm that case 1 is correct (for example, if the place has
        // been re-assigned in `other`)
        let same_place =
            |self_place: MaybeRemotePlace<'tcx>, to_place: MaybeRemotePlace<'tcx>| match (
                self_place, to_place,
            ) {
                (MaybeRemotePlace::Local(self_place), MaybeRemotePlace::Local(to_place)) => {
                    if self_place.place() != to_place.place() {
                        return false;
                    }
                    if self_place.location() == to_place.location() {
                        return true;
                    }
                    self_place.is_current()
                        && to_place.location().unwrap() == self.latest.get(self_place.place())
                }
                (MaybeRemotePlace::Remote(p1), MaybeRemotePlace::Remote(p2)) => p1 == p2,
                _ => false,
            };

        let same_cg_node =
            |self_place: CGNode<'tcx>, to_place: CGNode<'tcx>| match (self_place, to_place) {
                (CGNode::RegionProjection(rp1), CGNode::RegionProjection(rp2)) => {
                    same_place(rp1.place.into(), rp2.place.into()) && rp1.region() == rp2.region()
                }
                (CGNode::RemotePlace(rp1), CGNode::RemotePlace(rp2)) => rp1 == rp2,
                _ => false,
            };

        let same_local_node =
            |self_node: LocalNode<'tcx>, to_node: LocalNode<'tcx>| match (self_node, to_node) {
                (LocalNode::Place(p1), LocalNode::Place(p2)) => same_place(p1.into(), p2.into()),
                (LocalNode::RegionProjection(rp1), LocalNode::RegionProjection(rp2)) => {
                    same_cg_node(rp1.into(), rp2.into())
                }
                _ => false,
            };

        let same_pcg_node =
            |self_node: PCGNode<'tcx>, to_node: PCGNode<'tcx>| match (self_node, to_node) {
                (PCGNode::Place(p1), PCGNode::Place(p2)) => same_place(p1.into(), p2.into()),
                (PCGNode::RegionProjection(rp1), PCGNode::RegionProjection(rp2)) => {
                    same_cg_node(rp1.into(), rp2.into())
                }
                _ => false,
            };

        // TODO: perhaps this logic could be simplified?

        'outer: for exp in self
            .borrow_pcg_expansions()
            .difference(&to.borrow_pcg_expansions())
        {
            if exp.value.base().is_current() {
                for to in to.borrow_pcg_expansions() {
                    if same_local_node(exp.value.base().into(), to.value.base().into()) {
                        continue 'outer;
                    }
                }
            }
            ug.kill_edge(
                exp.clone().into(),
                self,
                repacker,
                UnblockType::ForExclusive,
            );
        }

        'outer: for self_abstraction in self.abstraction_edges() {
            'inner: for to_abstraction in to.abstraction_edges() {
                let self_value = self_abstraction.value.abstraction_type.clone();
                let to_value = to_abstraction.value.abstraction_type.clone();
                for (n1, n2) in self_value.inputs().iter().zip(to_value.inputs().iter()) {
                    if !same_cg_node(*n1, *n2) {
                        continue 'inner;
                    }
                }
                for (n1, n2) in self_value.outputs().iter().zip(to_value.outputs().iter()) {
                    if !same_cg_node((*n1).into(), (*n2).into()) {
                        continue 'inner;
                    }
                }
                continue 'outer;
            }
            ug.kill_edge(
                self_abstraction.clone().into(),
                self,
                repacker,
                UnblockType::ForExclusive,
            );
        }

        'outer: for self_member in self.graph.region_projection_members().iter() {
            'inner: for to_member in to.graph.region_projection_members().iter() {
                // Check if inputs match
                for (self_input, to_input) in self_member
                    .value
                    .inputs
                    .iter()
                    .zip(to_member.value.inputs.iter())
                {
                    if !same_pcg_node(*self_input, *to_input) {
                        // Some input doesn't match, try the next edge in to_graph
                        continue 'inner;
                    }
                }

                // Check if outputs match
                for (self_output, to_output) in self_member
                    .value
                    .outputs
                    .iter()
                    .zip(to_member.value.outputs.iter())
                {
                    if !same_local_node(*self_output, *to_output) {
                        // Some output doesn't match, try the next edge in to_graph
                        continue 'inner;
                    }
                }

                // All edges match, continue to the next edge in *self_graph*
                continue 'outer;
            }
            ug.kill_edge(
                self_member.clone().into(),
                self,
                repacker,
                UnblockType::ForExclusive,
            );
        }

        let mut weakens: FxHashSet<Weaken<'tcx>> = FxHashSet::default();
        let mut restores: FxHashSet<RestoreCapability<'tcx>> = FxHashSet::default();
        for (place, capability) in self.place_capabilities() {
            if let Some(to_capability) = to.get_capability(place) {
                if capability > to_capability {
                    weakens.insert(Weaken(place.clone(), capability, to_capability));
                } else if to_capability.is_exclusive() && capability.is_lent_exclusive() {
                    restores.insert(RestoreCapability(place, capability));
                }
            }
        }

        BorrowsBridge {
            added_borrows,
            expands,
            ug,
            weakens,
            restores,
            added_region_projection_members,
        }
    }

    /// Ensures that the place is expanded to the given place, with a certain
    /// capability.
    ///
    /// This also handles corresponding region projections of the place.
    #[must_use]
    #[instrument(skip(self, repacker), fields())]
    pub(crate) fn ensure_expansion_to(
        &mut self,
        repacker: PlaceRepacker<'_, 'tcx>,
        place: Place<'tcx>,
        location: Location,
        capability: CapabilityKind,
    ) -> ExecutedActions<'tcx> {
        let mut actions = ExecutedActions::new();
        let graph_edges = self.graph.edges().cloned().collect::<Vec<_>>();
        for p in graph_edges {
            match p.kind() {
                BorrowPCGEdgeKind::Borrow(reborrow) => match reborrow.assigned_ref {
                    MaybeOldPlace::Current {
                        place: assigned_place,
                    } if place.is_prefix(assigned_place) && !place.is_ref(repacker) => {
                        for ra in place.region_projections(repacker) {
                            self.record_and_apply_action(
                                BorrowPCGAction::add_region_projection_member(
                                    RegionProjectionMember::new(
                                        Coupled::singleton(reborrow.blocked_place.into()),
                                        Coupled::singleton(ra.into()),
                                    ),
                                    PathConditions::new(location.block),
                                    "Ensure Expansion To",
                                ),
                                &mut actions,
                                repacker,
                            );
                        }
                    }
                    _ => {}
                },
                _ => {}
            }
        }

        let unblock_type = if capability == CapabilityKind::Read {
            UnblockType::ForRead
        } else {
            UnblockType::ForExclusive
        };

        let mut ug = UnblockGraph::new();
        ug.unblock_node(place.into(), self, repacker, unblock_type);
        for rp in place.region_projections(repacker) {
            ug.unblock_node(rp.into(), self, repacker, unblock_type);
        }

        // The place itself could be in the owned PCG, but we want to unblock
        // the borrowed parts. For example if the place is a struct S, with
        // owned fields S.f and S.g, we will want to unblock S.f and S.g.
        for root_node in self.roots(repacker) {
            if let Some(root_node_place) = root_node.as_current_place() {
                if place.is_prefix(root_node_place) {
                    ug.unblock_node(root_node.into(), self, repacker, unblock_type);
                }
            }
        }

        for action in ug.actions(repacker) {
            actions.extend(self.apply_unblock_action(
                action,
                repacker,
                location,
                &format!("Ensure Expansion To {:?}", place),
            ));
        }

        let extra_acts =
            self.ensure_expansion_to_at_least(place.into(), repacker, location, capability);
        actions.extend(extra_acts);
        actions
    }

    #[must_use]
    #[instrument(skip(self, repacker), fields())]
    fn ensure_expansion_to_at_least(
        &mut self,
        to_place: Place<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
        location: Location,
        capability: CapabilityKind,
    ) -> ExecutedActions<'tcx> {
        let mut actions = ExecutedActions::new();
        let mut projects_from = None;

        for (base, _) in to_place.iter_projections() {
            let base: Place<'tcx> = base.into();
            let base = base.with_inherent_region(repacker);
            let (target, mut expansion, kind) = base.expand_one_level(to_place, repacker);
            match kind {
                ProjectionKind::Field(field_idx) => {
                    expansion.insert(field_idx.index(), target);
                }
                _ => {
                    expansion.push(target);
                }
            }
            if let ty::TyKind::Ref(region, _, mutbl) = base.ty(repacker).ty.kind() {
                projects_from = Some(mutbl);
                self.record_and_apply_action(
                    BorrowPCGAction::add_region_projection_member(
                        RegionProjectionMember::new(
                            Coupled::singleton(
                                RegionProjection::new((*region).into(), base).into(),
                            ),
                            Coupled::singleton(target.into()),
                        ),
                        PathConditions::new(location.block),
                        "Ensure Deref Expansion To At Least",
                    ),
                    &mut actions,
                    repacker,
                );
            }
            for rp in base.region_projections(repacker) {
                let dest_places = expansion
                    .iter()
                    .filter(|e| {
                        e.region_projections(repacker)
                            .into_iter()
                            .any(|child_rp| rp.region() == child_rp.region())
                    })
                    .copied()
                    .collect::<Vec<_>>();
                if dest_places.len() > 0 {
                    self.record_and_apply_action(
                        BorrowPCGAction::insert_borrow_pcg_expansion(
                            BorrowPCGExpansion::from_borrowed_base(
                                rp.into(),
                                BorrowExpansion::from_places(base, dest_places, repacker),
                                repacker,
                            ),
                            location,
                        ),
                        &mut actions,
                        repacker,
                    );
                }
            }
            if projects_from.is_some() {
                let origin_place: MaybeOldPlace<'tcx> = base.into();
                if !self.graph.contains_borrow_pcg_expansion_from(origin_place) {
                    let action = BorrowPCGAction::insert_borrow_pcg_expansion(
                        BorrowPCGExpansion::new(
                            origin_place.into(),
                            BorrowExpansion::from_places(base, expansion, repacker),
                            repacker,
                        ),
                        location,
                    );
                    self.record_and_apply_action(action, &mut actions, repacker);
                }
            }
        }
        if let Some(mutbl) = projects_from {
            self.set_capability(
                to_place,
                if mutbl.is_mut() {
                    CapabilityKind::Exclusive
                } else {
                    CapabilityKind::Read
                },
            );
        }
        actions
    }

    pub(crate) fn roots(&self, repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<PCGNode<'tcx>> {
        self.graph.roots(repacker)
    }

    #[must_use]
    pub(crate) fn apply_unblock_action(
        &mut self,
        action: BorrowPCGUnblockAction<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
        location: Location,
        context: &str,
    ) -> ExecutedActions<'tcx> {
        self.remove_edge_and_set_latest(&action.edge(), location, repacker, context)
    }

    pub(crate) fn apply_unblock_graph(
        &mut self,
        graph: UnblockGraph<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
        location: Location,
    ) -> ExecutedActions<'tcx> {
        let mut actions = ExecutedActions::new();
        for action in graph.actions(repacker) {
            actions.extend(self.apply_unblock_action(action, repacker, location, "Unblock Graph"));
        }
        actions
    }

    pub(crate) fn get_latest(&self, place: Place<'tcx>) -> SnapshotLocation {
        self.latest.get(place)
    }

    #[must_use]
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
    /// would not remove the *x -> y edge until this function is called at bb0[3].
    /// This ensures that the edge appears in the graph at the end of bb0[2]
    /// (rather than never at all).
    ///
    /// Additional caveat: we do not remove dead places that are function
    /// arguments. At least for now this interferes with the implementation in
    /// the Prusti purified encoding for accessing the final value of a
    /// reference-typed function argument in its postcondition.
    pub(super) fn pack_old_and_dead_leaves(
        &mut self,
        repacker: PlaceRepacker<'_, 'tcx>,
        location: Location,
        bc: &impl BorrowCheckerInterface<'tcx>,
    ) -> ExecutedActions<'tcx> {
        let mut actions = ExecutedActions::new();
        let prev_location = if location.statement_index == 0 {
            None
        } else {
            Some(Location {
                block: location.block,
                statement_index: location.statement_index - 1,
            })
        };
        let should_trim = |p: &PCGNode<'tcx, MaybeOldPlace<'tcx>>| {
            if p.is_old() {
                return true;
            }
            let p = match p {
                PCGNode::Place(p) => p.place(),
                PCGNode::RegionProjection(rp) => rp.place.place(),
            };
            if p.projection.is_empty() && repacker.is_arg(p.local) {
                return false;
            }
            prev_location.is_some() && !bc.is_live(p.into(), prev_location.unwrap())
        };
        loop {
            let mut cont = false;
            let edges = self.graph.leaf_edges(repacker);
            for edge in edges {
                let blocked_by_nodes = edge.blocked_by_nodes(repacker);
                if blocked_by_nodes.iter().all(should_trim) {
                    actions.extend(self.remove_edge_and_set_latest(
                        &edge,
                        location,
                        repacker,
                        &format!("Trim Old Leaves (blocked by: {:?})", blocked_by_nodes),
                    ));
                    cont = true;
                }
            }
            if !cont {
                break actions;
            }
        }
    }

    #[must_use]
    pub(crate) fn add_borrow(
        &mut self,
        blocked_place: MaybeRemotePlace<'tcx>,
        assigned_place: Place<'tcx>,
        mutability: Mutability,
        location: Location,
        region: ty::Region<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> ExecutedActions<'tcx> {
        assert!(
            assigned_place.ty(repacker).ty.ref_mutability().is_some(),
            "{:?}:{:?} Assigned place {:?} is not a reference. Ty: {:?}",
            repacker.body().source.def_id(),
            location,
            assigned_place,
            assigned_place.ty(repacker).ty
        );
        let mut actions = ExecutedActions::new();
        let (blocked_cap, assigned_cap) = match mutability {
            Mutability::Not => (CapabilityKind::Read, CapabilityKind::Read),
            Mutability::Mut => (CapabilityKind::Lent, CapabilityKind::Exclusive),
        };
        let borrow_edge = BorrowEdge::new(
            blocked_place.into(),
            assigned_place.into(),
            mutability,
            location,
            region,
            repacker,
        );
        let rp = borrow_edge.assigned_region_projection(repacker);
        self.record_and_apply_action(
            BorrowPCGAction::add_region_projection_member(
                RegionProjectionMember::new(
                    Coupled::singleton(rp.into()),
                    Coupled::singleton(assigned_place.into()),
                ),
                PathConditions::new(location.block),
                "Add Borrow",
            ),
            &mut actions,
            repacker,
        );
        self.set_capability(rp, blocked_cap);
        self.graph
            .insert(borrow_edge.to_borrow_pcg_edge(PathConditions::AtBlock(location.block)));

        if !blocked_place.is_owned(repacker) {
            self.set_capability(blocked_place, blocked_cap);
        }
        self.set_capability(assigned_place, assigned_cap);
        actions
    }

    pub(crate) fn has_borrow_at_location(&self, location: Location) -> bool {
        self.graph.has_borrow_at_location(location)
    }

    pub(crate) fn abstraction_edges(&self) -> FxHashSet<Conditioned<AbstractionEdge<'tcx>>> {
        self.graph.abstraction_edges()
    }

    #[must_use]
    pub(crate) fn insert_abstraction_edge(
        &mut self,
        abstraction: AbstractionEdge<'tcx>,
        block: BasicBlock,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> ExecutedActions<'tcx> {
        let mut actions = ExecutedActions::new();
        match &abstraction.abstraction_type {
            AbstractionType::FunctionCall(function_call_abstraction) => {
                for edge in function_call_abstraction.edges() {
                    for input in edge.inputs() {
                        self.set_capability(input, CapabilityKind::Lent);
                    }
                    for output in edge.outputs() {
                        self.set_capability(output, CapabilityKind::Exclusive);
                        if output.place.is_ref(repacker) {
                            let action = BorrowPCGAction::insert_borrow_pcg_expansion(
                                ExpansionOfOwned::new(output.place).into(),
                                function_call_abstraction.location(),
                            );
                            let result = self.apply_action(action.clone(), repacker);
                            actions.record(action, result);
                        }
                    }
                }
            }
            _ => todo!(),
        }
        self.graph
            .insert(abstraction.to_borrow_pcg_edge(PathConditions::new(block)));
        actions
    }

    pub(crate) fn make_place_old(
        &mut self,
        place: Place<'tcx>,
        _repacker: PlaceRepacker<'_, 'tcx>,
        debug_ctx: Option<DebugCtx>,
    ) -> bool {
        self.graph.make_place_old(place, &self.latest, debug_ctx)
    }
}
