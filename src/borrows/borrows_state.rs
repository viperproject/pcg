use crate::{
    borrows::{
        borrows_graph::borrows_imgcat_debug,
        edge_data::EdgeData,
        region_projection_member::RegionProjectionMemberKind,
    }, combined_pcs::{PCGError, PCGNode, PCGNodeLike}, rustc_interface::{
        ast::Mutability,
        data_structures::fx::FxHashSet,
        middle::{
            mir::{BasicBlock, BorrowKind, Location, MutBorrowKind},
            ty::{self},
        },
    }, utils::{
        display::DebugLines,
        join_lattice_verifier::{HasBlock, JoinLatticeVerifier},
        validity::HasValidityCheck,
        HasPlace,
    }, validity_checks_enabled, visualization::{dot_graph::DotGraph, generate_borrows_dot_graph}
};

use super::{
    borrow_pcg_action::BorrowPCGAction,
    borrow_pcg_capabilities::BorrowPCGCapabilities,
    borrow_pcg_edge::{
        BlockedNode, BorrowPCGEdge, BorrowPCGEdgeLike, BorrowPCGEdgeRef, LocalNode, ToBorrowsEdge,
    },
    borrow_pcg_expansion::{BorrowExpansion, BorrowPCGExpansion},
    borrows_graph::{BorrowsGraph, Conditioned, FrozenGraphRef},
    borrows_visitor::BorrowPCGActions,
    coupling_graph_constructor::BorrowCheckerInterface,
    has_pcs_elem::HasPcsElems,
    latest::Latest,
    path_condition::{PathCondition, PathConditions},
    region_projection::RegionProjection,
    region_projection_member::RegionProjectionMember,
    unblock_graph::{BorrowPCGUnblockAction, UnblockGraph, UnblockType},
};
use crate::borrows::edge::abstraction::AbstractionType;
use crate::borrows::edge::borrow::BorrowEdge;
use crate::borrows::edge::kind::BorrowPCGEdgeKind;
use crate::utils::place::maybe_old::MaybeOldPlace;
use crate::utils::place::maybe_remote::MaybeRemotePlace;
use crate::{
    free_pcs::CapabilityKind,
    utils::{Place, PlaceRepacker, SnapshotLocation},
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

#[cfg(debug_assertions)]
#[derive(Debug, Clone, PartialEq, Eq)]
struct JoinTransitionElem<'tcx> {
    block: BasicBlock,
    latest: Latest<'tcx>,
    graph: BorrowsGraph<'tcx>,
    capabilities: BorrowPCGCapabilities<'tcx>,
}

#[cfg(debug_assertions)]
impl<'tcx> HasBlock for JoinTransitionElem<'tcx> {
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
    pub(crate) capabilities: BorrowPCGCapabilities<'tcx>,
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

impl<'tcx> Eq for BorrowsState<'tcx> {}

impl<'tcx> PartialEq for BorrowsState<'tcx> {
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

impl<'tcx> Default for BorrowsState<'tcx> {
    fn default() -> Self {
        Self {
            latest: Latest::new(),
            graph: BorrowsGraph::new(),
            capabilities: BorrowPCGCapabilities::new(),
            #[cfg(debug_assertions)]
            join_transitions: JoinLatticeVerifier::new(),
        }
    }
}

#[derive(Debug)]
pub(crate) enum ExpansionReason {
    MoveOperand,
    CopyOperand,
    FakeRead,
    AssignTarget,
    CreateReference(BorrowKind),
    CreatePtr(Mutability),
    /// Just to read the place, but not refer to it
    RValueSimpleRead,
}

impl ExpansionReason {
    pub(crate) fn min_post_expansion_capability(&self) -> CapabilityKind {
        match self {
            ExpansionReason::MoveOperand => CapabilityKind::Exclusive,
            ExpansionReason::CopyOperand => CapabilityKind::Read,
            ExpansionReason::FakeRead => CapabilityKind::Read,
            ExpansionReason::AssignTarget => CapabilityKind::Write,
            ExpansionReason::CreateReference(borrow_kind) => match borrow_kind {
                BorrowKind::Shared => CapabilityKind::LentShared,
                BorrowKind::Fake(_) => unreachable!(),
                BorrowKind::Mut { kind } => match kind {
                    MutBorrowKind::Default => CapabilityKind::Exclusive,
                    MutBorrowKind::TwoPhaseBorrow => CapabilityKind::LentShared,
                    MutBorrowKind::ClosureCapture => CapabilityKind::Exclusive,
                },
            },
            ExpansionReason::CreatePtr(mutability) => {
                if mutability.is_mut() {
                    CapabilityKind::Exclusive
                } else {
                    CapabilityKind::LentShared
                }
            }
            ExpansionReason::RValueSimpleRead => CapabilityKind::Read,
        }
    }
}

impl<'tcx> BorrowsState<'tcx> {
    pub(crate) fn insert(&mut self, edge: BorrowPCGEdge<'tcx>) -> bool {
        self.graph.insert(edge)
    }
    pub(super) fn remove(&mut self, edge: &BorrowPCGEdge<'tcx>) -> bool {
        self.graph.remove(edge)
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

    pub(crate) fn contains_edge(&self, edge: &BorrowPCGEdge<'tcx>) -> bool {
        self.graph.contains_edge(edge)
    }

    pub(crate) fn graph_edges<'slf>(
        &'slf self,
    ) -> impl Iterator<Item = BorrowPCGEdgeRef<'tcx, 'slf>> {
        self.graph.edges()
    }

    pub(crate) fn graph(&self) -> &BorrowsGraph<'tcx> {
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
        self.capabilities.insert(node, capability)
    }

    #[must_use]
    pub(crate) fn remove_capability<T: PCGNodeLike<'tcx>>(&mut self, node: T) -> bool {
        self.capabilities.remove(node)
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
        if self
            .graph
            .join(&other.graph, self_block, other_block, repacker, bc)
        {
            changed = true;
        }
        if self.latest.join(&other.latest, self_block, repacker) {
            // TODO: Setting changed to true causes analysis to diverge
            // think about how latest should work in loops

            // changed = true;
        }
        if self.capabilities.join(&other.capabilities) {
            changed = true;
        }
        // // These checks are disabled even for debugging currently because they are very expensive
        // if changed && cfg!(debug_assertions) {
        //     debug_assert_ne!(*self, old);
        //     self.join_transitions.record_join_result(
        //         JoinComputation {
        //             lhs: old.join_transition_elem(self_block),
        //             rhs: other.clone().join_transition_elem(other_block),
        //             result: self.clone().join_transition_elem(self_block),
        //         },
        //         repacker,
        //     );
        // }
        changed
    }

    #[must_use]
    pub(crate) fn change_pcs_elem<T: 'tcx>(
        &mut self,
        old: T,
        new: T,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool
    where
        T: PartialEq + Clone,
        BorrowPCGEdge<'tcx>: HasPcsElems<T>,
    {
        self.graph.change_pcs_elem(old, new, repacker)
    }

    #[must_use]
    pub(super) fn remove_edge_and_set_latest(
        &mut self,
        edge: impl BorrowPCGEdgeLike<'tcx>,
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
        let remove_edge_action = BorrowPCGAction::remove_edge(edge.to_owned_edge(), context);
        let result = self.apply_action(remove_edge_action.clone(), repacker);
        actions.record(remove_edge_action, result);
        // If removing the edge results in a leaf node with a Lent capability, this
        // it should be set to Exclusive, as it is no longer being lent.
        if result {
            for node in self.graph.leaf_nodes(repacker, None) {
                if self.get_capability(node.into()) == Some(CapabilityKind::Lent) {
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
        let edges = self
            .edges_blocking(place.into(), repacker)
            .into_iter()
            .map(|e| e.to_owned_edge())
            .collect::<Vec<_>>();
        if edges.is_empty() {
            return actions;
        }
        for edge in edges {
            actions.extend(self.remove_edge_and_set_latest(
                edge,
                location,
                repacker,
                "Delete Descendants",
            ));
        }
        actions
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

    pub(crate) fn edges_blocked_by<'slf, 'mir: 'slf>(
        &'slf self,
        node: LocalNode<'tcx>,
        repacker: PlaceRepacker<'mir, 'tcx>,
    ) -> FxHashSet<BorrowPCGEdgeRef<'tcx, 'slf>> {
        self.graph.edges_blocked_by(node, repacker).collect()
    }

    pub(crate) fn borrows(&self) -> FxHashSet<Conditioned<BorrowEdge<'tcx>>> {
        self.graph.borrows()
    }

    /// Ensures that the place is expanded to the given place, with a certain
    /// capability.
    ///
    /// This also handles corresponding region projections of the place.
    #[must_use]
    pub(crate) fn ensure_expansion_to(
        &mut self,
        repacker: PlaceRepacker<'_, 'tcx>,
        place: Place<'tcx>,
        location: Location,
        expansion_reason: ExpansionReason,
    ) -> Result<ExecutedActions<'tcx>, PCGError> {
        let mut actions = ExecutedActions::new();

        let graph_edges = self
            .graph
            .edges()
            .map(|e| e.to_owned_edge())
            .collect::<Vec<_>>();

        // If we are going to contract a place, borrows may need to be converted
        // to region projection member edges. For example, if the type of `x.t` is
        // `&'a mut T` and there is a borrow `x.t = &mut y`, and we need to expand to `x`, then we need
        // to replace the borrow edge with an edge `{y} -> {x↓'a}`.
        for p in graph_edges {
            match p.kind() {
                BorrowPCGEdgeKind::Borrow(borrow) => match borrow.assigned_ref {
                    MaybeOldPlace::Current {
                        place: assigned_place,
                    } if place.is_prefix(assigned_place) && !place.is_ref(repacker) => {
                        for ra in place.region_projections(repacker) {
                            self.record_and_apply_action(
                                BorrowPCGAction::add_region_projection_member(
                                    RegionProjectionMember::new(
                                        vec![borrow.blocked_place.into()],
                                        vec![ra.into()],
                                        RegionProjectionMemberKind::Ref,
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

        let unblock_type = match expansion_reason {
            ExpansionReason::MoveOperand => UnblockType::ForRead,
            ExpansionReason::CopyOperand => UnblockType::ForExclusive,
            ExpansionReason::FakeRead => UnblockType::ForRead,
            ExpansionReason::AssignTarget => UnblockType::ForExclusive,
            ExpansionReason::CreateReference(borrow_kind) => match borrow_kind {
                BorrowKind::Shared => UnblockType::ForRead,
                BorrowKind::Fake(_) => unreachable!(),
                BorrowKind::Mut { kind } => match kind {
                    MutBorrowKind::Default => UnblockType::ForExclusive,
                    MutBorrowKind::TwoPhaseBorrow => UnblockType::ForRead,
                    MutBorrowKind::ClosureCapture => UnblockType::ForExclusive,
                },
            },
            ExpansionReason::CreatePtr(mutability) => {
                if mutability == Mutability::Mut {
                    UnblockType::ForExclusive
                } else {
                    UnblockType::ForRead
                }
            }
            ExpansionReason::RValueSimpleRead => UnblockType::ForRead,
        };

        let mut ug = UnblockGraph::new();
        ug.unblock_node(place.to_pcg_node(), self, repacker, unblock_type);
        for rp in place.region_projections(repacker) {
            ug.unblock_node(rp.to_pcg_node(), self, repacker, unblock_type);
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
        let unblock_actions = ug.actions(repacker).unwrap_or_else(|e| {
            if borrows_imgcat_debug() {
                let dot_graph = generate_borrows_dot_graph(repacker, self.graph()).unwrap();
                DotGraph::render_with_imgcat(&dot_graph, "Borrows graph for unblock actions")
                    .unwrap_or_else(|e| {
                        eprintln!("Error rendering borrows graph: {}", e);
                    });
            }
            panic!(
                "Error when ensuring expansion to {:?} for {:?}: {:?}",
                place, expansion_reason, e
            );
        });
        for action in unblock_actions {
            actions.extend(self.apply_unblock_action(
                action,
                repacker,
                location,
                &format!("Ensure Expansion To {:?}", place),
            ));
        }

        if self.contains(place, repacker) {
            if self.get_capability(place.into()) == None {
                let expected_capability = expansion_reason.min_post_expansion_capability();
                self.record_and_apply_action(
                    BorrowPCGAction::restore_capability(place.into(), expected_capability),
                    &mut actions,
                    repacker,
                );
            }
        } else {
            let extra_acts = self.ensure_expansion_to_at_least(place.into(), repacker, location)?;
            actions.extend(extra_acts);
        }

        Ok(actions)
    }

    /// Inserts edges to ensure that the borrow PCG is expanded to at least
    /// `to_place`. We assume that any unblock operations have already been
    /// performed.
    #[must_use]
    fn ensure_expansion_to_at_least(
        &mut self,
        to_place: Place<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
        location: Location,
    ) -> Result<ExecutedActions<'tcx>, PCGError> {
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
                    vec![RegionProjection::new((*region).into(), base, repacker).to_pcg_node()],
                    vec![target.into()],
                    RegionProjectionMemberKind::DerefRegionProjection,
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

            if !target.is_owned(repacker) {
                let expansion = BorrowPCGExpansion::new(
                    base.into(),
                    BorrowExpansion::from_places(expansion.clone(), repacker),
                    repacker,
                );

                if !self.contains_edge(
                    &expansion
                        .clone()
                        .to_borrow_pcg_edge(PathConditions::AtBlock(location.block)),
                ) {
                    let action = BorrowPCGAction::insert_borrow_pcg_expansion(
                        expansion,
                        location,
                        "Ensure Deref Expansion (Place)",
                    );
                    self.record_and_apply_action(action, &mut actions, repacker);
                }
            }

            for rp in base.region_projections(repacker) {
                let dest_places = expansion
                    .iter()
                    .filter(|e| {
                        e.region_projections(repacker)
                            .into_iter()
                            .any(|child_rp| rp.region(repacker) == child_rp.region(repacker))
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
        self.remove_edge_and_set_latest(action.edge, location, repacker, context)
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
    pub(super) fn pack_old_and_dead_leaves<'slf, 'mir>(
        &'slf mut self,
        repacker: PlaceRepacker<'mir, 'tcx>,
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
        let mut num_edges_prev = self.graph.num_edges();
        'outer: loop {
            fn go<'slf, 'mir, 'tcx>(
                slf: &'slf mut BorrowsState<'tcx>,
                repacker: PlaceRepacker<'mir, 'tcx>,
                prev_location: Option<Location>,
                bc: &impl BorrowCheckerInterface<'tcx>,
            ) -> Option<BorrowPCGEdge<'tcx>> {
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

                for edge in fg
                    .leaf_edges(repacker)
                    .into_iter()
                    .map(|e| e.to_owned_edge())
                {
                    let blocked_by_nodes = edge.blocked_by_nodes(repacker);
                    if blocked_by_nodes.iter().all(|p| should_trim(*p, &fg)) {
                        return Some(edge);
                    }
                }
                None
            }
            if let Some(edge) = go(self, repacker, prev_location, bc) {
                actions.extend(self.remove_edge_and_set_latest(
                    edge,
                    location,
                    repacker,
                    "Trim Old Leaves",
                ));
                assert!(self.graph.num_edges() < num_edges_prev);
                num_edges_prev = self.graph.num_edges();
                continue 'outer;
            }
            break;
        }
        actions
    }

    pub(crate) fn add_borrow(
        &mut self,
        blocked_place: MaybeRemotePlace<'tcx>,
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
        let borrow_edge = BorrowEdge::new(
            blocked_place.into(),
            assigned_place.into(),
            kind.mutability(),
            location,
            region,
            repacker,
        );
        let rp = borrow_edge.assigned_region_projection(repacker);
        self.set_capability(rp.into(), assigned_cap, repacker);
        assert!(self
            .graph
            .insert(borrow_edge.to_borrow_pcg_edge(PathConditions::AtBlock(location.block))));

        // Update the capability of the blocked place, if necessary
        if !blocked_place.is_owned(repacker) {
            match kind {
                BorrowKind::Mut {
                    kind: MutBorrowKind::Default,
                } => {
                    if self.get_capability(blocked_place.into()) != Some(CapabilityKind::Lent) {
                        assert!(self.set_capability(
                            blocked_place.into(),
                            CapabilityKind::Lent,
                            repacker
                        ));
                    }
                }
                _ => {
                    match self.get_capability(blocked_place.into()) {
                        Some(CapabilityKind::Exclusive | CapabilityKind::Lent) => {
                            assert!(self.set_capability(
                                blocked_place.into(),
                                CapabilityKind::LentShared,
                                repacker
                            ));
                        }
                        Some(CapabilityKind::Read | CapabilityKind::LentShared) => {
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

        // self.set_capability(assigned_place, assigned_cap, repacker);
    }

    /// Inserts the abstraction edge and sets capabilities for
    /// inputs and outputs: input capabilities are set to [`CapabilityKind::Lent`]
    /// outputs are set to [`CapabilityKind::Exclusive`]
    pub(crate) fn insert_abstraction_edge(
        &mut self,
        abstraction: AbstractionType<'tcx>,
        block: BasicBlock,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) {
        match &abstraction {
            AbstractionType::FunctionCall(function_call_abstraction) => {
                for edge in function_call_abstraction.edges() {
                    for input in edge.inputs() {
                        self.set_capability(input.into(), CapabilityKind::Lent, repacker);
                    }
                    for output in edge.outputs() {
                        self.set_capability(output.into(), CapabilityKind::Exclusive, repacker);
                    }
                }
            }
            _ => todo!(),
        }
        assert!(self
            .graph
            .insert(abstraction.to_borrow_pcg_edge(PathConditions::new(block))));
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
