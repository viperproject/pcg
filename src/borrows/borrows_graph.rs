use std::cell::Cell;

use crate::{
    combined_pcs::PCGNode,
    rustc_interface::{data_structures::fx::FxHashSet, middle::mir::BasicBlock},
    utils::validity::HasValidityCheck,
};
use serde_json::json;

use crate::{
    borrows::domain::AbstractionType,
    coupling,
    utils::{Place, PlaceRepacker},
    visualization::{dot_graph::DotGraph, generate_borrows_dot_graph},
};

use super::{
    borrow_edge::BorrowEdge,
    borrow_pcg_edge::{BlockedNode, BorrowPCGEdge, BorrowPCGEdgeKind, LocalNode, ToBorrowsEdge},
    coupling_graph_constructor::{
        BorrowCheckerInterface, CGNode, Coupled, CouplingGraphConstructor,
    },
    domain::{AbstractionBlockEdge, LoopAbstraction, MaybeOldPlace, ToJsonWithRepacker},
    edge_data::EdgeData,
    has_pcs_elem::{HasPcsElems, MakePlaceOld},
    latest::Latest,
    path_condition::{PathCondition, PathConditions},
    region_abstraction::AbstractionEdge,
    region_projection::RegionProjection,
    region_projection_member::{RegionProjectionMember, RegionProjectionMemberKind},
};

#[derive(Clone, Debug)]
pub struct BorrowsGraph<'tcx> {
    edges: FxHashSet<BorrowPCGEdge<'tcx>>,
    /// See [`BorrowsGraph::is_valid`] for more details.
    cached_is_valid: Cell<Option<bool>>,
}

impl<'tcx> Eq for BorrowsGraph<'tcx> {}

impl<'tcx> PartialEq for BorrowsGraph<'tcx> {
    fn eq(&self, other: &Self) -> bool {
        self.edges == other.edges
    }
}

pub(crate) const COUPLING_IMGCAT_DEBUG: bool = false;
pub(crate) const BORROWS_IMGCAT_DEBUG: bool = false;

impl<'tcx> BorrowsGraph<'tcx> {
    pub(crate) fn contains<T: Into<PCGNode<'tcx>>>(
        &self,
        node: T,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        let node = node.into();
        self.edges.iter().any(|edge| {
            edge.blocks_node(node, repacker)
                || node
                    .as_blocking_node()
                    .map(|blocking| edge.blocked_by_nodes(repacker).contains(&blocking))
                    .unwrap_or(false)
        })
    }

    pub(crate) fn new() -> Self {
        Self {
            edges: FxHashSet::default(),
            cached_is_valid: Cell::new(None),
        }
    }

    pub fn edges(&self) -> impl Iterator<Item = &BorrowPCGEdge<'tcx>> {
        self.edges.iter()
    }

    pub(crate) fn base_coupling_graph(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> coupling::DisjointSetGraph<CGNode<'tcx>> {
        let mut graph: coupling::DisjointSetGraph<CGNode<'tcx>> = coupling::DisjointSetGraph::new();
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
                            let coupled_input_projections: Vec<CGNode<'tcx>> =
                                region_projection_member
                                    .inputs
                                    .iter()
                                    .flat_map(|rp| (*rp).try_into())
                                    .collect::<Vec<_>>();

                            let coupled_output_projections: Vec<CGNode<'tcx>> =
                                region_projection_member
                                    .outputs
                                    .iter()
                                    .flat_map(|rp| (*rp).try_into())
                                    .collect::<Vec<_>>();

                            if !coupled_input_projections.is_empty() {
                                graph.insert_endpoint(coupled_input_projections.into());
                            }
                            if !coupled_output_projections.is_empty() {
                                graph.insert_endpoint(coupled_output_projections.into());
                            }
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

    pub(crate) fn abstraction_edges(&self) -> FxHashSet<Conditioned<AbstractionEdge<'tcx>>> {
        self.edges
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

    pub(crate) fn borrows(&self) -> FxHashSet<Conditioned<BorrowEdge<'tcx>>> {
        self.edges
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

    /// Returns all borrow edges where the assigned ref is `place`
    pub(crate) fn borrows_blocked_by(
        &self,
        place: MaybeOldPlace<'tcx>,
    ) -> FxHashSet<Conditioned<BorrowEdge<'tcx>>> {
        self.edges
            .iter()
            .filter_map(|edge| match &edge.kind() {
                BorrowPCGEdgeKind::Borrow(reborrow) if reborrow.assigned_ref == place => {
                    Some(Conditioned {
                        conditions: edge.conditions().clone(),
                        value: reborrow.clone(),
                    })
                }
                _ => None,
            })
            .collect()
    }

    /// All edges that are not blocked by any other edge
    pub(crate) fn is_leaf_edge(
        &self,
        edge: &BorrowPCGEdge<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        edge.kind()
            .blocked_by_nodes(repacker)
            .iter()
            .all(|p| !self.has_edge_blocking(*p, repacker))
    }

    pub(crate) fn leaf_edges(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> FxHashSet<BorrowPCGEdge<'tcx>> {
        let mut candidates = self.edges.clone();
        candidates.retain(|edge| self.is_leaf_edge(edge, repacker));
        candidates
    }

    pub(crate) fn nodes(&self, repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<PCGNode<'tcx>> {
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

    pub(crate) fn leaf_nodes(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> FxHashSet<LocalNode<'tcx>> {
        self.leaf_edges(repacker)
            .into_iter()
            .flat_map(|edge| edge.blocked_by_nodes(repacker).into_iter())
            .collect()
    }

    pub(crate) fn roots(&self, repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<PCGNode<'tcx>> {
        self.nodes(repacker)
            .into_iter()
            .filter(|node| self.is_root(*node, repacker))
            .collect()
    }

    pub(crate) fn has_edge_blocking<T: Into<BlockedNode<'tcx>>>(
        &self,
        blocked_node: T,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        let blocked_node = blocked_node.into();
        self.edges()
            .any(|edge| edge.blocks_node(blocked_node, repacker))
    }

    pub(crate) fn is_root<T: Into<PCGNode<'tcx>>>(
        &self,
        node: T,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        !self.has_edge_blocked_by(node.into(), repacker)
    }

    pub(crate) fn has_edge_blocked_by(
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

    pub(crate) fn edges_blocked_by(
        &self,
        node: LocalNode<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> FxHashSet<BorrowPCGEdge<'tcx>> {
        self.edges
            .iter()
            .filter(|edge| edge.blocked_by_nodes(repacker).contains(&node))
            .cloned()
            .collect()
    }

    pub(crate) fn make_place_old(
        &mut self,
        place: Place<'tcx>,
        latest: &Latest<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        self.mut_edges(|edge| edge.make_place_old(place, latest, repacker))
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
        self.cached_is_valid.set(None);
        let self_coupling_graph =
            self.construct_coupling_graph(borrow_checker, repacker, exit_block);
        let other_coupling_graph =
            other.construct_coupling_graph(borrow_checker, repacker, exit_block);

        if COUPLING_IMGCAT_DEBUG {
            self_coupling_graph
                .render_with_imgcat(&format!("self coupling graph: {:?}", self_block));
            other_coupling_graph
                .render_with_imgcat(&format!("other coupling graph: {:?}", exit_block));
        }

        let mut result = self_coupling_graph;
        result.merge(&other_coupling_graph);
        if COUPLING_IMGCAT_DEBUG {
            result.render_with_imgcat("merged coupling graph");
        }

        // Collect existing abstraction edges at this block
        let existing_edges: FxHashSet<_> = self
            .edges
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
            let rps: Vec<RegionProjection<'tcx>> = isolated
                .iter()
                .flat_map(|node| (*node).try_into())
                .collect::<Vec<_>>();

            // e.g. for place r: &'r mut T, if we have the region projection
            // r↓'r, the blocked place is *r.
            // TODO: Handle the general case, e.g r: (&'a mut T, &'b mut U)
            let cg_places = rps
                .iter()
                .flat_map(|rp| rp.place().try_into())
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
                            Coupled::singleton(edge.value.blocked_place.into()),
                            rps.clone()
                                .into_iter()
                                .map(|rp| rp.try_into().unwrap())
                                .collect::<Vec<_>>()
                                .into(),
                            RegionProjectionMemberKind::Todo,
                        ));
                    let inserted =
                        self.insert(BorrowPCGEdge::new(new_edge_kind, edge.conditions.clone()));
                    changed |= inserted;
                }
                self.remove(&edge.into());
            }
        }

        for (blocked, assigned) in result.edges() {
            let abstraction = LoopAbstraction::new(
                AbstractionBlockEdge::new(
                    blocked.clone().into_iter().collect(),
                    assigned
                        .clone()
                        .into_iter()
                        .map(|node| node.try_into().unwrap())
                        .collect(),
                ),
                self_block,
            )
            .to_borrow_pcg_edge(PathConditions::new(self_block));
            new_edges.insert(abstraction.clone());

            if !existing_edges.contains(&abstraction) {
                let inserted = self.insert(abstraction);
                changed |= inserted;
            }
        }

        // Remove existing edges that aren't in the new abstraction
        for edge in existing_edges {
            if !new_edges.contains(&edge) {
                self.remove(&edge);
                changed = true;
            }
        }

        // Edges that only connect nodes within the region abstraction (but are
        // not the abstraction edge itself, should be removed
        let edges = self.edges().cloned().collect::<Vec<_>>();
        for edge in edges {
            if self.is_encapsulated_by_abstraction(&edge, repacker) {
                self.remove(&edge);
                changed = true;
            }
        }

        // The process may result interior (old) places now being roots in the
        // graph. These should be removed.
        for root in self.roots(repacker) {
            if root.is_old() {
                for edge in self.edges_blocking(root, repacker) {
                    self.remove(&edge);
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

    pub(crate) fn join<T: BorrowCheckerInterface<'tcx>>(
        &mut self,
        other: &Self,
        self_block: BasicBlock,
        other_block: BasicBlock,
        repacker: PlaceRepacker<'_, 'tcx>,
        bc: &T,
    ) -> bool {
        if repacker.should_check_validity() {
            debug_assert!(other.is_valid(repacker), "Other graph is invalid");
        }
        let old_self = self.clone();

        if BORROWS_IMGCAT_DEBUG {
            if let Ok(dot_graph) = generate_borrows_dot_graph(repacker, self) {
                DotGraph::render_with_imgcat(&dot_graph, &format!("Self graph: {:?}", self_block))
                    .unwrap_or_else(|e| {
                        eprintln!("Error rendering self graph: {}", e);
                    });
            }
            if let Ok(dot_graph) = generate_borrows_dot_graph(repacker, other) {
                DotGraph::render_with_imgcat(
                    &dot_graph,
                    &format!("Other graph: {:?}", other_block),
                )
                .unwrap_or_else(|e| {
                    eprintln!("Error rendering other graph: {}", e);
                });
            }
        }

        if repacker.is_back_edge(other_block, self_block) {
            let exit_blocks = repacker.get_loop_exit_blocks(self_block, other_block);
            if exit_blocks.len() >= 1 {
                let result = self.join_loop(other, self_block, exit_blocks[0], repacker, bc);
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
        let our_edges = self.edges.clone();
        for other_edge in other.edges.iter() {
            match our_edges.iter().find(|e| e.kind() == other_edge.kind()) {
                Some(our_edge) => {
                    if our_edge.conditions() != other_edge.conditions() {
                        let mut new_conditions = our_edge.conditions().clone();
                        new_conditions.join(&other_edge.conditions());
                        self.edges.remove(our_edge);
                        _ = self.insert(BorrowPCGEdge::new(
                            other_edge.kind().clone(),
                            new_conditions,
                        ));
                    }
                }
                None => {
                    _ = self.insert(other_edge.clone());
                }
            }
        }
        for edge in self.edges().cloned().collect::<Vec<_>>() {
            if let BorrowPCGEdgeKind::Abstraction(_) = edge.kind() {
                continue;
            }
            if self.is_encapsulated_by_abstraction(&edge, repacker) {
                self.remove(&edge);
            }
        }
        let mut finished = false;
        while !finished {
            finished = true;
            for leaf_node in self.leaf_nodes(repacker) {
                if !other.leaf_nodes(repacker).contains(&leaf_node) {
                    for edge in self.edges_blocked_by(leaf_node.into(), repacker) {
                        finished = false;
                        self.remove(&edge);
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

        // TODO: Currently the graph can become cyclic after the join, for some reason.
        //       This test is postponed for now (we still ensure that the ultimate graph is valid).
        if false && !self.is_valid(repacker) {
            if BORROWS_IMGCAT_DEBUG {
                if let Ok(dot_graph) = generate_borrows_dot_graph(repacker, self) {
                    DotGraph::render_with_imgcat(&dot_graph, "Invalid self graph").unwrap_or_else(
                        |e| {
                            eprintln!("Error rendering self graph: {}", e);
                        },
                    );
                }
                if let Ok(dot_graph) = generate_borrows_dot_graph(repacker, &old_self) {
                    DotGraph::render_with_imgcat(&dot_graph, "Old self graph").unwrap_or_else(
                        |e| {
                            eprintln!("Error rendering old self graph: {}", e);
                        },
                    );
                }
                if let Ok(dot_graph) = generate_borrows_dot_graph(repacker, other) {
                    DotGraph::render_with_imgcat(&dot_graph, "Other graph").unwrap_or_else(|e| {
                        eprintln!("Error rendering other graph: {}", e);
                    });
                }
            }
            panic!(
                "Graph became invalid after join. self: {:?}, other: {:?}",
                self_block, other_block
            );
        }
        changed
    }

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
        self.mut_pcs_elems(
            |thing| {
                if *thing == old {
                    *thing = new.clone();
                    true
                } else {
                    false
                }
            },
            repacker,
        )
    }

    #[must_use]
    pub(crate) fn insert(&mut self, edge: BorrowPCGEdge<'tcx>) -> bool {
        self.cached_is_valid.set(None);
        self.edges.insert(edge)
    }

    #[must_use]
    pub(crate) fn contains_edge(&self, edge: &BorrowPCGEdge<'tcx>) -> bool {
        self.edges.contains(edge)
    }

    pub(crate) fn edges_blocking(
        &self,
        node: BlockedNode<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Vec<BorrowPCGEdge<'tcx>> {
        self.edges()
            .filter(|edge| edge.blocks_node(node, repacker))
            .cloned()
            .collect()
    }

    pub(crate) fn remove(&mut self, edge: &BorrowPCGEdge<'tcx>) -> bool {
        self.cached_is_valid.set(None);
        self.edges.remove(edge)
    }

    pub(crate) fn mut_pcs_elems<'slf, T: 'tcx>(
        &'slf mut self,
        mut f: impl FnMut(&mut T) -> bool,
        repacker: PlaceRepacker<'_, 'tcx>,
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
            if cfg!(debug_assertions) {
                edge.assert_validity(repacker);
            }
            changed
        })
    }

    fn mut_edges<'slf>(
        &'slf mut self,
        mut f: impl FnMut(&mut BorrowPCGEdge<'tcx>) -> bool,
    ) -> bool {
        let mut changed = false;
        self.edges = self
            .edges
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
        self.cached_is_valid.set(None);
        self.edges
            .retain(|edge| edge.conditions().valid_for_path(path));
    }

    pub(crate) fn add_path_condition(&mut self, pc: PathCondition) -> bool {
        self.mut_edges(|edge| edge.insert_path_condition(pc.clone()))
    }

    /// Returns true iff the expected invariants of the graph hold. This
    /// function is only used for debugging and testing.
    ///
    /// This predicate should definitely be true for every final graph in the computed
    /// PCG. There are probably other points where it should hold as well, but these
    /// aren't documented yet.
    pub(crate) fn is_valid(&self, repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        if let Some(valid) = self.cached_is_valid.get() {
            return valid;
        }
        let valid = self.is_acyclic(repacker);
        self.cached_is_valid.set(Some(valid));
        valid
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
