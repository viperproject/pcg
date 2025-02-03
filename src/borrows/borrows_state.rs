use tracing::instrument;

use crate::{
    borrows::{edge_data::EdgeData, region_projection_member::RegionProjectionMemberKind},
    rustc_interface::{
        ast::Mutability,
        data_structures::fx::FxHashSet,
        middle::{
            mir::{BasicBlock, Location},
            ty::{self},
        },
    },
    utils::HasPlace,
};

use crate::{
    free_pcs::CapabilityKind,
    utils::{Place, PlaceRepacker, SnapshotLocation},
};

use super::{
    borrow_edge::BorrowEdge,
    borrow_pcg_action::BorrowPCGAction,
    borrow_pcg_capabilities::BorrowPCGCapabilities,
    borrow_pcg_edge::{
        BlockedNode, BorrowPCGEdge, BorrowPCGEdgeKind, LocalNode, PCGNode, ToBorrowsEdge,
    },
    borrow_pcg_expansion::{BorrowExpansion, BorrowPCGExpansion},
    borrows_graph::{BorrowsGraph, Conditioned},
    borrows_visitor::{BorrowPCGActions, DebugCtx},
    coupling_graph_constructor::{BorrowCheckerInterface, Coupled},
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
    actions: BorrowPCGActions<'tcx>,
    changed: bool,
}

impl<'tcx> ExecutedActions<'tcx> {
    fn new() -> Self {
        Self {
            actions: BorrowPCGActions::new(),
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

    pub(super) fn actions(self) -> BorrowPCGActions<'tcx> {
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
    pub(crate) fn debug_capability_lines(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Vec<String> {
        self.capabilities.debug_capability_lines(repacker)
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

    pub(crate) fn contains_edge(&self, edge: &BorrowPCGEdge<'tcx>) -> bool {
        self.graph.contains_edge(edge)
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
    #[must_use]
    pub(crate) fn set_capability<T: Into<PCGNode<'tcx>> + std::fmt::Debug>(
        &mut self,
        node: T,
        capability: CapabilityKind,
    ) -> bool {
        self.capabilities.insert(node, capability)
    }

    #[must_use]
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
                    self.record_and_apply_action(
                        BorrowPCGAction::restore_capability(node.into(), CapabilityKind::Exclusive),
                        &mut actions,
                        repacker,
                    );
                }
            }
        }
        actions
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

    pub(crate) fn borrows(&self) -> FxHashSet<Conditioned<BorrowEdge<'tcx>>> {
        self.graph.borrows()
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
    ) -> Result<ExecutedActions<'tcx>, String> {
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
                                        RegionProjectionMemberKind::Todo,
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

        let extra_acts = self.ensure_expansion_to_at_least(place.into(), repacker, location)?;
        actions.extend(extra_acts);
        Ok(actions)
    }

    #[must_use]
    #[instrument(skip(self, repacker), fields())]
    fn ensure_expansion_to_at_least(
        &mut self,
        to_place: Place<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
        location: Location,
    ) -> Result<ExecutedActions<'tcx>, String> {
        let mut actions = ExecutedActions::new();

        for (base, _) in to_place.iter_projections() {
            let base: Place<'tcx> = base.into();
            let base = base.with_inherent_region(repacker);
            let (target, mut expansion, kind) = base.expand_one_level(to_place, repacker)?;
            kind.insert_target_into_expansion(target, &mut expansion);

            if let ty::TyKind::Ref(region, _, _) = base.ty(repacker).ty.kind() {
                // This is a dereference, taking the the form t -> *t where t
                // has type &'a T. We insert a region projection member for t↓'a
                // -> *t if it doesn't already exist.

                let region_projection_member = RegionProjectionMember::new(
                    Coupled::singleton(RegionProjection::new((*region).into(), base).into()),
                    Coupled::singleton(target.into()),
                    RegionProjectionMemberKind::Todo,
                );

                let path_conditions = PathConditions::new(location.block);

                if !self.contains_edge(&BorrowPCGEdge::new(
                    region_projection_member.clone().into(),
                    path_conditions.clone(),
                )) {
                    self.record_and_apply_action(
                        BorrowPCGAction::add_region_projection_member(
                            region_projection_member,
                            PathConditions::new(location.block),
                            "Ensure Deref Expansion To At Least",
                        ),
                        &mut actions,
                        repacker,
                    );
                }
            }

            let origin_place: MaybeOldPlace<'tcx> = base.into();
            if !origin_place.is_owned(repacker)
                && !self.graph.contains_borrow_pcg_expansion_from(origin_place)
            {
                let action = BorrowPCGAction::insert_borrow_pcg_expansion(
                    BorrowPCGExpansion::new(
                        origin_place.into(),
                        BorrowExpansion::from_places(expansion.clone(), repacker),
                        repacker,
                    ),
                    location,
                    "Ensure Deref Expansion (Place)",
                );
                self.record_and_apply_action(action, &mut actions, repacker);
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
                    let expansion = BorrowPCGExpansion::from_borrowed_base(
                        rp.into(),
                        BorrowExpansion::from_places(dest_places, repacker),
                        repacker,
                    );
                    let path_conditions = PathConditions::new(location.block);
                    if !self.contains_edge(&expansion.clone().to_borrow_pcg_edge(path_conditions)) {
                        self.record_and_apply_action(
                            BorrowPCGAction::insert_borrow_pcg_expansion(
                                expansion,
                                location,
                                "Ensure Deref Expansion (Region Projection)",
                            ),
                            &mut actions,
                            repacker,
                        );
                    }
                }
            }
        }
        Ok(actions)
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
    /// would not remove the *x -> y edge until this function is called at `bb0[3]`.
    /// This ensures that the edge appears in the graph at the end of `bb0[2]`
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
                let is_expansion_leaf = match &edge.kind() {
                    BorrowPCGEdgeKind::BorrowPCGExpansion(de) => {
                        !de.is_owned_expansion()
                            && de
                                .expansion(repacker)
                                .into_iter()
                                .all(|p| !self.graph.has_edge_blocking(p, repacker))
                    }
                    _ => false,
                };
                if is_expansion_leaf {
                    actions.extend(self.remove_edge_and_set_latest(
                        &edge,
                        location,
                        repacker,
                        &format!("Trim Old Leaves (expansion leaf)"),
                    ));
                    cont = true;
                } else {
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
                    RegionProjectionMemberKind::Todo,
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

    /// Inserts the abstraction edge and sets capabilities for
    /// inputs and outputs: input capabilities are set to [`CapabilityKind::Lent`]
    /// outputs are set to [`CapabilityKind::Exclusive`]
    pub(crate) fn insert_abstraction_edge(
        &mut self,
        abstraction: AbstractionEdge<'tcx>,
        block: BasicBlock,
    ) {
        match &abstraction.abstraction_type {
            AbstractionType::FunctionCall(function_call_abstraction) => {
                for edge in function_call_abstraction.edges() {
                    for input in edge.inputs() {
                        self.set_capability(input, CapabilityKind::Lent);
                    }
                    for output in edge.outputs() {
                        self.set_capability(output, CapabilityKind::Exclusive);
                    }
                }
            }
            _ => todo!(),
        }
        self.graph
            .insert(abstraction.to_borrow_pcg_edge(PathConditions::new(block)));
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
