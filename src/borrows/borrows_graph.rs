use rustc_interface::{
    data_structures::fx::FxHashSet,
    middle::mir::{BasicBlock, Location},
};
use serde_json::json;

use crate::{
    borrows::domain::AbstractionType,
    coupling,
    free_pcs::CapabilityKind,
    rustc_interface,
    utils::{Place, PlaceRepacker},
    visualization::{dot_graph::DotGraph, generate_borrows_dot_graph},
};

use super::{
    borrow_edge::BorrowEdge,
    borrow_pcg_edge::{
        BlockedNode, BorrowPCGEdge, BorrowPCGEdgeKind, LocalNode, PCGNode, ToBorrowsEdge,
    },
    borrows_visitor::DebugCtx,
    coupling_graph_constructor::{
        BorrowCheckerInterface, CGNode, Coupled, CouplingGraphConstructor,
    },
    deref_expansion::{DerefExpansion, OwnedExpansion},
    domain::{
        AbstractionBlockEdge, LoopAbstraction, MaybeOldPlace, MaybeRemotePlace, ToJsonWithRepacker,
    },
    edge_data::EdgeData,
    has_pcs_elem::{HasPcsElems, MakePlaceOld},
    latest::Latest,
    path_condition::{PathCondition, PathConditions},
    region_abstraction::AbstractionEdge,
    region_projection_member::{RegionProjectionMember, RegionProjectionMemberDirection},
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BorrowsGraph<'tcx>(FxHashSet<BorrowPCGEdge<'tcx>>);

const COUPLING_IMGCAT_DEBUG: bool = false;
const BORROWS_IMGCAT_DEBUG: bool = false;

impl<'tcx> BorrowsGraph<'tcx> {
    pub fn contains_edge(&self, edge: &BorrowPCGEdgeKind<'tcx>) -> bool {
        self.0.iter().any(|e| e.kind() == edge)
    }

    pub fn contains<T: Into<PCGNode<'tcx>>>(
        &self,
        node: T,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        let node = node.into();
        self.0.iter().any(|edge| {
            edge.blocks_node(node, repacker)
                || node
                    .as_blocking_node()
                    .map(|blocking| edge.blocked_by_nodes(repacker).contains(&blocking))
                    .unwrap_or(false)
        })
    }
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn new() -> Self {
        Self(FxHashSet::default())
    }

    pub fn edge_count(&self) -> usize {
        self.0.len()
    }

    pub fn edges(&self) -> impl Iterator<Item = &BorrowPCGEdge<'tcx>> {
        self.0.iter()
    }

    pub fn base_coupling_graph(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> coupling::DisjointSetGraph<CGNode<'tcx>> {
        let mut graph = coupling::DisjointSetGraph::new();
        // TODO: For performance, we could not track the path in release mode,
        // we only use it to detect infinite loops
        #[derive(Clone)]
        struct ExploreFrom<'tcx> {
            path: Vec<PCGNode<'tcx>>,
        }

        impl<'tcx> ExploreFrom<'tcx> {
            pub fn new(current: PCGNode<'tcx>) -> Self {
                Self {
                    path: vec![current],
                }
            }

            pub fn connect(&self) -> Option<CGNode<'tcx>> {
                self.path.iter().rev().find_map(|node| node.as_cg_node())
            }

            pub fn current(&self) -> PCGNode<'tcx> {
                self.path.last().unwrap().clone()
            }

            pub fn extend(&self, node: PCGNode<'tcx>) -> Option<Self> {
                let mut result = self.clone();
                if result.path.contains(&node) {
                    panic!("Cycle detected: {:?} already in {:?}", node, result.path);
                }
                result.path.push(node);
                Some(result)
            }
        }

        let mut queue = vec![];
        for node in self.roots(repacker) {
            queue.push(ExploreFrom::new(node.into()));
        }

        while let Some(ef) = queue.pop() {
            let edges_blocking = self.edges_blocking(ef.current(), repacker);
            for edge in edges_blocking {
                match edge.kind() {
                    BorrowPCGEdgeKind::Abstraction(abstraction_edge) => {
                        let inputs = abstraction_edge
                            .inputs()
                            .into_iter()
                            .map(|node| node.into())
                            .collect::<Vec<_>>()
                            .into();
                        let outputs = abstraction_edge
                            .outputs()
                            .into_iter()
                            .map(|node| node.into())
                            .collect::<Vec<_>>()
                            .into();
                        graph.add_edge(&inputs, &outputs);
                    }
                    _ => {
                        // RegionProjectionMember edges may contain coupled
                        // nodes (via `[RegionProjectionMember.projections]`)
                        // These nodes may not have any edges in the coupling
                        // graph but must be included anyway.
                        if let BorrowPCGEdgeKind::RegionProjectionMember(region_projection_member) =
                            edge.kind()
                        {
                            graph.insert_endpoint(
                                region_projection_member
                                    .projections
                                    .iter()
                                    .map(|rp| (*rp).into())
                                    .collect::<Vec<_>>()
                                    .into(),
                            );
                        }
                        for node in edge.blocked_by_nodes(repacker) {
                            if let LocalNode::RegionProjection(rp) = node {
                                if let Some(source) = ef.connect() {
                                    graph.add_edge(&vec![source].into(), &vec![rp.into()].into());
                                }
                            }
                        }
                    }
                }
                for node in edge.blocked_by_nodes(repacker) {
                    if let Some(ef) = ef.extend(node.into()) {
                        queue.push(ef);
                    }
                }
            }
        }
        graph
    }

    pub (crate) fn region_projection_members(
        &self,
    ) -> FxHashSet<Conditioned<RegionProjectionMember<'tcx>>> {
        self.0
            .iter()
            .filter_map(|edge| match &edge.kind() {
                BorrowPCGEdgeKind::RegionProjectionMember(member) => Some(Conditioned {
                    conditions: edge.conditions().clone(),
                    value: member.clone(),
                }),
                _ => None,
            })
            .collect()
    }

    pub fn abstraction_edges(&self) -> FxHashSet<Conditioned<AbstractionEdge<'tcx>>> {
        self.0
            .iter()
            .filter_map(|edge| match &edge.kind() {
                BorrowPCGEdgeKind::Abstraction(abstraction) => Some(Conditioned {
                    conditions: edge.conditions().clone(),
                    value: abstraction.clone(),
                }),
                _ => None,
            })
            .collect()
    }

    pub fn deref_expansions(&self) -> FxHashSet<Conditioned<DerefExpansion<'tcx>>> {
        self.0
            .iter()
            .filter_map(|edge| match &edge.kind() {
                BorrowPCGEdgeKind::DerefExpansion(de) => Some(Conditioned {
                    conditions: edge.conditions().clone(),
                    value: de.clone(),
                }),
                _ => None,
            })
            .collect()
    }

    pub fn borrows(&self) -> FxHashSet<Conditioned<BorrowEdge<'tcx>>> {
        self.0
            .iter()
            .filter_map(|edge| match &edge.kind() {
                BorrowPCGEdgeKind::Borrow(reborrow) => Some(Conditioned {
                    conditions: edge.conditions().clone(),
                    value: reborrow.clone(),
                }),
                _ => None,
            })
            .collect()
    }

    pub fn has_borrow_at_location(&self, location: Location) -> bool {
        self.0.iter().any(|edge| match &edge.kind() {
            BorrowPCGEdgeKind::Borrow(reborrow) => reborrow.reserve_location() == location,
            _ => false,
        })
    }
    pub fn borrows_blocking(
        &self,
        place: MaybeRemotePlace<'tcx>,
    ) -> FxHashSet<Conditioned<BorrowEdge<'tcx>>> {
        self.0
            .iter()
            .filter_map(|edge| match &edge.kind() {
                BorrowPCGEdgeKind::Borrow(reborrow) => {
                    if reborrow.blocked_place == place {
                        Some(Conditioned {
                            conditions: edge.conditions().clone(),
                            value: reborrow.clone(),
                        })
                    } else {
                        None
                    }
                }
                _ => None,
            })
            .collect()
    }

    pub fn borrows_blocked_by(
        &self,
        place: MaybeOldPlace<'tcx>,
    ) -> FxHashSet<Conditioned<BorrowEdge<'tcx>>> {
        self.0
            .iter()
            .filter_map(|edge| match &edge.kind() {
                BorrowPCGEdgeKind::Borrow(reborrow) => {
                    if reborrow.assigned_place == place {
                        Some(Conditioned {
                            conditions: edge.conditions().clone(),
                            value: reborrow.clone(),
                        })
                    } else {
                        None
                    }
                }
                _ => None,
            })
            .collect()
    }

    /// All edges that are not blocked by any other edge
    pub fn is_leaf_edge(
        &self,
        edge: &BorrowPCGEdge<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        edge.kind()
            .blocked_by_nodes(repacker)
            .iter()
            .all(|p| !self.has_edge_blocking(*p, repacker))
    }

    pub fn leaf_edges(&self, repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<BorrowPCGEdge<'tcx>> {
        let mut candidates = self.0.clone();
        candidates.retain(|edge| self.is_leaf_edge(edge, repacker));
        candidates
    }

    pub fn nodes(&self, repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<PCGNode<'tcx>> {
        self.edges()
            .flat_map(|edge| {
                edge.blocked_nodes(repacker).into_iter().chain(
                    edge.blocked_by_nodes(repacker)
                        .into_iter()
                        .map(|node| node.into()),
                )
            })
            .collect()
    }

    pub fn leaf_nodes(&self, repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<LocalNode<'tcx>> {
        self.leaf_edges(repacker)
            .into_iter()
            .flat_map(|edge| edge.blocked_by_nodes(repacker).into_iter())
            .collect()
    }

    pub fn roots(&self, repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<PCGNode<'tcx>> {
        self.nodes(repacker)
            .into_iter()
            .filter(|node| self.is_root(*node, repacker))
            .collect()
    }

    pub fn has_edge_blocking<T: Into<BlockedNode<'tcx>>>(
        &self,
        blocked_node: T,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        let blocked_node = blocked_node.into();
        self.edges()
            .any(|edge| edge.blocks_node(blocked_node, repacker))
    }

    pub fn is_root<T: Into<PCGNode<'tcx>>>(
        &self,
        node: T,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        !self.has_edge_blocked_by(node.into(), repacker)
    }

    pub fn has_edge_blocked_by(
        &self,
        node: PCGNode<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        match node.as_local_node() {
            Some(node) => self
                .edges()
                .any(|edge| edge.blocked_by_nodes(repacker).contains(&node)),
            None => false,
        }
    }

    pub fn edges_blocked_by(
        &self,
        node: LocalNode<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> FxHashSet<BorrowPCGEdge<'tcx>> {
        self.0
            .iter()
            .filter(|edge| edge.blocked_by_nodes(repacker).contains(&node))
            .cloned()
            .collect()
    }

    pub fn make_place_old(
        &mut self,
        place: Place<'tcx>,
        latest: &Latest<'tcx>,
        _debug_ctx: Option<DebugCtx>,
    ) {
        self.mut_edges(|edge| {
            edge.make_place_old(place, latest);
            true
        });
    }

    fn construct_coupling_graph<T: BorrowCheckerInterface<'tcx>>(
        &self,
        borrow_checker: &T,
        repacker: PlaceRepacker<'_, 'tcx>,
        block: BasicBlock,
    ) -> coupling::DisjointSetGraph<CGNode<'tcx>> {
        let constructor = CouplingGraphConstructor::new(borrow_checker, repacker, block);
        constructor.construct_coupling_graph(self)
    }

    fn join_loop<T: BorrowCheckerInterface<'tcx>>(
        &mut self,
        other: &Self,
        self_block: BasicBlock,
        exit_block: BasicBlock,
        repacker: PlaceRepacker<'_, 'tcx>,
        borrow_checker: &T,
    ) -> bool {
        let self_coupling_graph =
            self.construct_coupling_graph(borrow_checker, repacker, exit_block);
        let other_coupling_graph =
            other.construct_coupling_graph(borrow_checker, repacker, exit_block);

        if COUPLING_IMGCAT_DEBUG {
            self_coupling_graph.render_with_imgcat();
            other_coupling_graph.render_with_imgcat();
        }

        let mut result = self_coupling_graph;
        result.merge(&other_coupling_graph);
        if COUPLING_IMGCAT_DEBUG {
            result.render_with_imgcat();
        }

        // Collect existing abstraction edges at this block
        let existing_edges: FxHashSet<_> = self
            .0
            .iter()
            .filter(|edge| {
                if let BorrowPCGEdgeKind::Abstraction(abstraction_edge) = &edge.kind() {
                    if let AbstractionType::Loop(loop_abstraction) =
                        &abstraction_edge.abstraction_type
                    {
                        loop_abstraction.location().block == self_block
                    } else {
                        false
                    }
                } else {
                    false
                }
            })
            .cloned()
            .collect();

        // Create new abstraction edges from the merged coupling graph
        let mut new_edges = FxHashSet::default();
        let mut changed = false;

        // Borrow edges originally going through individual region projection
        // nodes should be moved to the corresponding coupled nodes.
        // TODO: Make sure `changed` is set correctly.
        for isolated in result.endpoints() {
            let rps = isolated
                .iter()
                .flat_map(|node| node.as_region_projection())
                .collect::<Vec<_>>();

            // e.g. for place r: &'r mut T, if we have the region projection
            // r↓'r, the blocked place is *r.
            // TODO: Handle the general case, e.g r: (&'a mut T, &'b mut U)
            let cg_places = rps
                .iter()
                .flat_map(|rp| rp.deref(repacker))
                .collect::<Vec<_>>();

            let edges_to_move = cg_places
                .iter()
                .flat_map(|p| {
                    self.borrows_blocked_by(*p)
                        .into_iter()
                        .chain(other.borrows_blocked_by(*p))
                })
                .collect::<Vec<_>>();
            for edge in edges_to_move {
                // If this edge would become a loop, it can be removed.
                if cg_places
                    .iter()
                    .all(|p| Some(*p) != edge.value.blocked_place.as_local_place())
                {
                    let new_edge_kind =
                        BorrowPCGEdgeKind::RegionProjectionMember(RegionProjectionMember::new(
                            edge.value.blocked_place,
                            rps.clone().into(),
                            RegionProjectionMemberDirection::ProjectionBlocksPlace,
                        ));
                    self.insert(BorrowPCGEdge::new(new_edge_kind, edge.conditions.clone()));
                }
                self.remove(&edge.into(), DebugCtx::Other);
            }
        }

        for (blocked, assigned) in result.edges() {
            let abstraction = LoopAbstraction::new(
                AbstractionBlockEdge::new(
                    blocked.clone().into_iter().collect(),
                    assigned
                        .clone()
                        .into_iter()
                        .map(|node| node.as_region_projection().unwrap())
                        .collect(),
                ),
                self_block,
            )
            .to_borrow_pcg_edge(PathConditions::new(self_block));
            new_edges.insert(abstraction.clone());

            if !existing_edges.contains(&abstraction) {
                self.insert(abstraction);
                changed = true;
            }
        }

        // Remove existing edges that aren't in the new abstraction
        for edge in existing_edges {
            if !new_edges.contains(&edge) {
                self.remove(&edge, DebugCtx::Other);
                changed = true;
            }
        }

        // Edges that only connect nodes within the region abstraction (but are
        // not the abstraction edge itself, should be removed
        let edges = self.edges().cloned().collect::<Vec<_>>();
        for edge in edges {
            if self.is_encapsulated_by_abstraction(&edge, repacker) {
                self.remove(&edge, DebugCtx::Other);
                changed = true;
            }
        }

        // The process may result interior (old) places now being roots in the
        // graph. These should be removed.
        for root in self.roots(repacker) {
            if root.is_old() {
                for edge in self.edges_blocking(root, repacker) {
                    self.remove(&edge, DebugCtx::Other);
                    changed = true;
                }
            }
        }

        changed
    }

    /// Returns true iff `edge` connects two nodes within an abstraction edge
    fn is_encapsulated_by_abstraction(
        &self,
        edge: &BorrowPCGEdge<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        'outer: for abstraction in self.abstraction_edges() {
            for blocked in edge.blocked_nodes(repacker) {
                if !abstraction.value.blocked_nodes(repacker).contains(&blocked) {
                    continue 'outer;
                }
            }
            for blocked_by in edge.blocked_by_nodes(repacker) {
                if !abstraction
                    .value
                    .blocked_by_nodes(repacker)
                    .contains(&blocked_by)
                {
                    continue 'outer;
                }
            }
            return true;
        }
        false
    }

    pub fn join<T: BorrowCheckerInterface<'tcx>>(
        &mut self,
        other: &Self,
        self_block: BasicBlock,
        other_block: BasicBlock,
        repacker: PlaceRepacker<'_, 'tcx>,
        region_liveness: &T,
    ) -> bool {
        let old_self = self.clone();

        if BORROWS_IMGCAT_DEBUG {
            if let Ok(dot_graph) = generate_borrows_dot_graph(repacker, self) {
                DotGraph::render_with_imgcat(&dot_graph, "Self graph:").unwrap_or_else(|e| {
                    eprintln!("Error rendering self graph: {}", e);
                });
            }
            if let Ok(dot_graph) = generate_borrows_dot_graph(repacker, other) {
                DotGraph::render_with_imgcat(&dot_graph, "Other graph:").unwrap_or_else(|e| {
                    eprintln!("Error rendering other graph: {}", e);
                });
            }
        }

        if repacker.is_back_edge(other_block, self_block) {
            let exit_blocks = repacker.get_loop_exit_blocks(self_block, other_block);
            if exit_blocks.len() >= 1 {
                let result =
                    self.join_loop(other, self_block, exit_blocks[0], repacker, region_liveness);
                if BORROWS_IMGCAT_DEBUG {
                    if let Ok(dot_graph) = generate_borrows_dot_graph(repacker, self) {
                        DotGraph::render_with_imgcat(
                            &dot_graph,
                            &format!("After join (loop, changed={:?}):", result),
                        )
                        .unwrap_or_else(|e| {
                            eprintln!("Error rendering self graph: {}", e);
                        });
                    }
                }
                assert!(self.is_valid(repacker), "Graph became invalid after join");
                return result;
            }
            // TODO: Handle multiple exit blocks
        }
        let our_edges = self.0.clone();
        for other_edge in other.0.iter() {
            match our_edges.iter().find(|e| e.kind() == other_edge.kind()) {
                Some(our_edge) => {
                    if our_edge.conditions() != other_edge.conditions() {
                        let mut new_conditions = our_edge.conditions().clone();
                        new_conditions.join(&other_edge.conditions());
                        self.0.remove(our_edge);
                        self.insert(BorrowPCGEdge::new(
                            other_edge.kind().clone(),
                            new_conditions,
                        ));
                    }
                }
                None => {
                    match other_edge.kind() {
                        BorrowPCGEdgeKind::RegionProjectionMember(member)
                            if member.direction()
                                == RegionProjectionMemberDirection::ProjectionBlocksPlace =>
                        {
                            for projection in member.projections.iter() {
                                if let Some(place) = projection.deref(repacker) {
                                    for borrow in self.borrows_blocked_by(place) {
                                        // if borrow.value.blocked_place == member.place {
                                        self.remove(&(borrow.into()), DebugCtx::Other);
                                        // }
                                    }
                                }
                            }
                        }
                        _ => {}
                    }
                    self.insert(other_edge.clone());
                }
            }
        }
        for edge in self.edges().cloned().collect::<Vec<_>>() {
            if let BorrowPCGEdgeKind::Abstraction(_) = edge.kind() {
                continue;
            }
            if self.is_encapsulated_by_abstraction(&edge, repacker) {
                self.remove(&edge, DebugCtx::Other);
            }
        }
        let mut finished = false;
        while !finished {
            finished = true;
            for leaf_node in self.leaf_nodes(repacker) {
                if !other.leaf_nodes(repacker).contains(&leaf_node) {
                    for edge in self.edges_blocked_by(leaf_node.into(), repacker) {
                        finished = false;
                        self.remove(&edge, DebugCtx::Other);
                    }
                }
            }
        }

        let changed = old_self != *self;

        if BORROWS_IMGCAT_DEBUG {
            if let Ok(dot_graph) = generate_borrows_dot_graph(repacker, self) {
                DotGraph::render_with_imgcat(
                    &dot_graph,
                    &format!("After join: (changed={:?})", changed),
                )
                .unwrap_or_else(|e| {
                    eprintln!("Error rendering self graph: {}", e);
                });
            }
        }

        assert!(self.is_valid(repacker), "Graph became invalid after join");
        changed
    }

    pub fn change_pcs_elem<T: 'tcx>(&mut self, old: T, new: T) -> bool
    where
        T: PartialEq + Clone,
        BorrowPCGEdge<'tcx>: HasPcsElems<T>,
    {
        self.mut_pcs_elems(|thing| {
            if *thing == old {
                *thing = new.clone();
                true
            } else {
                false
            }
        })
    }

    pub fn insert(&mut self, edge: BorrowPCGEdge<'tcx>) -> bool {
        self.0.insert(edge)
    }

    pub fn edges_blocking(
        &self,
        node: BlockedNode<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Vec<BorrowPCGEdge<'tcx>> {
        self.edges()
            .filter(|edge| edge.blocks_node(node, repacker))
            .cloned()
            .collect()
    }

    pub fn remove_abstraction_at(&mut self, location: Location) {
        self.0.retain(|edge| {
            if let BorrowPCGEdgeKind::Abstraction(abstraction) = &edge.kind() {
                abstraction.location() != location
            } else {
                true
            }
        });
    }

    pub fn remove_region_projection_member(&mut self, member: RegionProjectionMember<'tcx>) {
        self.0.retain(|edge| {
            if let BorrowPCGEdgeKind::RegionProjectionMember(m) = &edge.kind() {
                m != &member
            } else {
                true
            }
        });
    }

    pub fn remove(&mut self, edge: &BorrowPCGEdge<'tcx>, _debug_ctx: DebugCtx) -> bool {
        self.0.remove(edge)
    }

    pub fn move_region_projection_member_projections(
        &mut self,
        old_projection_place: MaybeOldPlace<'tcx>,
        new_projection_place: MaybeOldPlace<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) {
        self.mut_edges(|edge| {
            if let BorrowPCGEdgeKind::RegionProjectionMember(member) = &mut edge.kind {
                for p in member.projections.iter_mut() {
                    if p.place == old_projection_place {
                        let idx = p.index(repacker);
                        *p = new_projection_place.region_projection(idx, repacker);
                    }
                }
            }
            true
        });
    }

    pub fn move_borrows(
        &mut self,
        orig_assigned_place: MaybeOldPlace<'tcx>,
        new_assigned_place: MaybeOldPlace<'tcx>,
    ) {
        self.mut_edges(|edge| {
            if let BorrowPCGEdgeKind::Borrow(reborrow) = &mut edge.kind {
                if reborrow.assigned_place == orig_assigned_place {
                    reborrow.assigned_place = new_assigned_place;
                }
            }
            true
        });
    }

    pub fn contains_deref_expansion_from(&self, place: &MaybeOldPlace<'tcx>) -> bool {
        self.0.iter().any(|edge| {
            if let BorrowPCGEdgeKind::DerefExpansion(de) = &edge.kind {
                de.base() == *place
            } else {
                false
            }
        })
    }

    /// If an expansion is added, returns the capability of the expanded place;
    /// i.e. `Exclusive` if the place is mutable, and `Read` otherwise.
    /// If there is no expansion added, returns `None`.
    pub(crate) fn ensure_deref_expansion_to_at_least(
        &mut self,
        to_place: Place<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
        location: Location,
    ) -> Option<CapabilityKind> {
        let mut projects_from = None;
        let mut changed = false;
        for (place, _) in to_place.iter_projections() {
            let place: Place<'tcx> = place.into();
            if let Some(mutbl) = place.ref_mutability(repacker) {
                projects_from = Some(mutbl);
            }
            let (target, mut expansion, _) = place.expand_one_level(to_place, repacker);
            expansion.push(target);
            if projects_from.is_some() {
                let origin_place: MaybeOldPlace<'tcx> = place.into();
                if !origin_place.place().is_owned(repacker)
                    && !self.contains_deref_expansion_from(&origin_place)
                {
                    self.insert_deref_expansion(origin_place, expansion, location, repacker);
                    changed = true;
                }
            }
        }
        if !changed {
            None
        } else {
            projects_from.map(|mutbl| {
                if mutbl.is_mut() {
                    CapabilityKind::Exclusive
                } else {
                    CapabilityKind::Read
                }
            })
        }
    }

    pub fn insert_owned_expansion(&mut self, place: MaybeOldPlace<'tcx>, location: Location) {
        let de = OwnedExpansion::new(place).into();
        self.insert(BorrowPCGEdge::new(de, PathConditions::new(location.block)));
    }

    fn insert_deref_expansion(
        &mut self,
        place: MaybeOldPlace<'tcx>,
        expansion: Vec<Place<'tcx>>,
        location: Location,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) {
        for p in expansion.iter() {
            assert!(p.projection.len() > place.place().projection.len());
        }
        if place.place().is_owned(repacker) {
            self.insert_owned_expansion(place, location);
        } else {
            let de = DerefExpansion::borrowed(place, expansion, location, repacker);
            self.insert(BorrowPCGEdge::new(
                BorrowPCGEdgeKind::DerefExpansion(de),
                PathConditions::new(location.block),
            ));
        }
    }

    pub(crate) fn mut_pcs_elems<'slf, T: 'tcx>(
        &'slf mut self,
        mut f: impl FnMut(&mut T) -> bool,
    ) -> bool
    where
        BorrowPCGEdge<'tcx>: HasPcsElems<T>,
    {
        self.mut_edges(|edge| {
            let mut changed = false;
            for rp in edge.pcs_elems() {
                if f(rp) {
                    changed = true;
                }
            }
            changed
        })
    }

    fn mut_edges<'slf>(
        &'slf mut self,
        mut f: impl FnMut(&mut BorrowPCGEdge<'tcx>) -> bool,
    ) -> bool {
        let mut changed = false;
        self.0 = self
            .0
            .drain()
            .map(|mut edge| {
                if f(&mut edge) {
                    changed = true;
                }
                edge
            })
            .collect();
        changed
    }

    pub fn filter_for_path(&mut self, path: &[BasicBlock]) {
        self.0.retain(|edge| edge.conditions().valid_for_path(path));
    }

    pub fn add_path_condition(&mut self, pc: PathCondition) -> bool {
        self.mut_edges(|edge| edge.insert_path_condition(pc.clone()))
    }

    pub fn is_valid(&self, repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        for node in self.roots(repacker) {
            match node {
                PCGNode::Place(place) => {
                    // If *x at l is an interiorn node, we still currently have
                    // x at l for the edge {x at l -> *x at l}. Except for these
                    // cases, we should not have any old places that are roots.
                    if place.is_old() && !place.is_owned(repacker) {
                        return false;
                    }
                }
                PCGNode::RegionProjection(region_projection) => {
                    if region_projection.place.is_old() {
                        return false;
                    }
                }
            }
        }
        self.is_acyclic(repacker)
    }

    fn is_acyclic(&self, repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        let mut visited = FxHashSet::default();
        let mut rec_stack = FxHashSet::default();

        fn has_cycle<'tcx>(
            graph: &BorrowsGraph<'tcx>,
            node: PCGNode<'tcx>,
            visited: &mut FxHashSet<PCGNode<'tcx>>,
            rec_stack: &mut FxHashSet<PCGNode<'tcx>>,
            repacker: PlaceRepacker<'_, 'tcx>,
        ) -> bool {
            if rec_stack.contains(&node) {
                return true;
            }

            if visited.contains(&node) {
                return false;
            }

            visited.insert(node.clone());
            rec_stack.insert(node.clone());

            for edge in graph.edges() {
                if edge.blocks_node(node.clone(), repacker) {
                    for blocked_node in edge.blocked_by_nodes(repacker) {
                        if has_cycle(graph, blocked_node.into(), visited, rec_stack, repacker) {
                            return true;
                        }
                    }
                }
            }

            rec_stack.remove(&node);
            false
        }

        for root in self.roots(repacker) {
            if has_cycle(self, root.into(), &mut visited, &mut rec_stack, repacker) {
                return false;
            }
        }

        true
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Conditioned<T> {
    pub conditions: PathConditions,
    pub value: T,
}

impl<T> Conditioned<T> {
    pub fn new(value: T, conditions: PathConditions) -> Self {
        Self { conditions, value }
    }
}

impl<'tcx, T: ToJsonWithRepacker<'tcx>> ToJsonWithRepacker<'tcx> for Conditioned<T> {
    fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        json!({
            "conditions": self.conditions.to_json(repacker),
            "value": self.value.to_json(repacker)
        })
    }
}
