pub mod aliases;

use smallvec::smallvec;
use std::{
    cell::{Ref, RefCell},
    collections::{HashMap, HashSet},
};

use crate::{
    combined_pcs::{PCGNode, PCGNodeLike},
    rustc_interface::{
        data_structures::fx::{FxHashMap, FxHashSet},
        middle::mir::{self, BasicBlock, TerminatorEdges},
    },
    utils::{
        display::{DebugLines, DisplayDiff, DisplayWithRepacker},
        validity::HasValidityCheck,
    },
    validity_checks_enabled,
};
use itertools::Itertools;
use serde_json::json;
use tracing::{span, Level};

use super::{
    borrow_pcg_edge::{
        BlockedNode, BorrowPCGEdge, BorrowPCGEdgeLike, BorrowPCGEdgeRef, LocalNode, ToBorrowsEdge,
    },
    coupling_graph_constructor::{BorrowCheckerInterface, CGNode, CouplingGraphConstructor},
    edge_data::EdgeData,
    has_pcs_elem::{HasPcsElems, MakePlaceOld},
    latest::Latest,
    path_condition::{PathCondition, PathConditions},
    region_projection::RegionProjection,
    region_projection_member::{
        RegionProjectionMember, RegionProjectionMemberKind, RegionProjectionMemberOutputs,
    },
};
use crate::borrow_pcg::edge::abstraction::{
    AbstractionBlockEdge, AbstractionType, LoopAbstraction,
};
use crate::borrow_pcg::edge::borrow::BorrowEdge;
use crate::borrow_pcg::edge::kind::BorrowPCGEdgeKind;
use crate::utils::json::ToJsonWithRepacker;
use crate::{
    coupling,
    utils::{env_feature_enabled, Place, PlaceRepacker},
    visualization::{dot_graph::DotGraph, generate_borrows_dot_graph},
};

#[derive(Clone, Debug)]
pub struct BorrowsGraph<'tcx> {
    edges: FxHashMap<BorrowPCGEdgeKind<'tcx>, PathConditions>,
    cached_leaf_nodes: RefCell<Option<FxHashSet<LocalNode<'tcx>>>>,
}

impl<'tcx> DebugLines<PlaceRepacker<'_, 'tcx>> for BorrowsGraph<'tcx> {
    fn debug_lines(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Vec<String> {
        self.edges()
            .map(|edge| format!("{}", edge.to_short_string(repacker)))
            .collect()
    }
}

impl<'tcx> HasValidityCheck<'tcx> for BorrowsGraph<'tcx> {
    fn check_validity(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Result<(), String> {
        tracing::debug!(
            "Checking acyclicity of borrows graph ({} edges)",
            self.edges.len()
        );
        if !self.is_acyclic(repacker) {
            return Err("Graph is not acyclic".to_string());
        }
        tracing::debug!("Acyclicity check passed");
        Ok(())
    }
}

impl<'tcx> Eq for BorrowsGraph<'tcx> {}

impl<'tcx> PartialEq for BorrowsGraph<'tcx> {
    fn eq(&self, other: &Self) -> bool {
        self.edges == other.edges
    }
}

pub(crate) fn coupling_imgcat_debug() -> bool {
    env_feature_enabled("PCG_COUPLING_DEBUG_IMGCAT").unwrap_or(false)
}

pub(crate) fn borrows_imgcat_debug() -> bool {
    env_feature_enabled("PCG_BORROWS_DEBUG_IMGCAT").unwrap_or(false)
}

impl<'tcx> BorrowsGraph<'tcx> {
    pub(crate) fn has_function_call_abstraction_at(&self, location: mir::Location) -> bool {
        for edge in self.edges() {
            match edge.kind() {
                BorrowPCGEdgeKind::Abstraction(abstraction) => {
                    if abstraction.is_function_call() && abstraction.location() == location {
                        return true;
                    }
                }
                _ => {}
            }
        }
        false
    }

    pub(crate) fn contains<T: Into<PCGNode<'tcx>>>(
        &self,
        node: T,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        let node = node.into();
        self.edges().any(|edge| {
            edge.blocks_node(node, repacker)
                || node
                    .as_blocking_node()
                    .map(|blocking| edge.blocked_by_nodes(repacker).contains(&blocking))
                    .unwrap_or(false)
        })
    }

    pub(crate) fn new() -> Self {
        Self {
            edges: FxHashMap::default(),
            cached_leaf_nodes: RefCell::new(None),
        }
    }

    pub fn edges<'slf>(&'slf self) -> impl Iterator<Item = BorrowPCGEdgeRef<'tcx, 'slf>> + 'slf {
        self.edges
            .iter()
            .map(|(kind, conditions)| BorrowPCGEdgeRef { kind, conditions })
    }

    pub(crate) fn base_coupling_graph(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> coupling::DisjointSetGraph<CGNode<'tcx>> {
        let mut graph: coupling::DisjointSetGraph<CGNode<'tcx>> = coupling::DisjointSetGraph::new();
        #[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
        struct ExploreFrom<'tcx> {
            current: PCGNode<'tcx>,
            connect: Option<CGNode<'tcx>>,
        }

        impl<'tcx> ExploreFrom<'tcx> {
            pub fn new(current: PCGNode<'tcx>) -> Self {
                Self {
                    current,
                    connect: current.as_cg_node(),
                }
            }

            pub fn connect(&self) -> Option<CGNode<'tcx>> {
                self.connect
            }

            pub fn current(&self) -> PCGNode<'tcx> {
                self.current
            }

            pub fn extend(&self, node: PCGNode<'tcx>) -> Self {
                Self {
                    current: node,
                    connect: node.as_cg_node().or(self.connect),
                }
            }
        }

        impl<'tcx> std::fmt::Display for ExploreFrom<'tcx> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(
                    f,
                    "Current: {}, Connect: {}",
                    self.current,
                    match self.connect {
                        Some(cg_node) => format!("{}", cg_node),
                        None => "None".to_string(),
                    }
                )
            }
        }

        let mut seen = HashSet::new();

        let mut queue = vec![];
        for node in self.roots(repacker) {
            queue.push(ExploreFrom::new(node.into()));
        }

        let blocking_map = FrozenGraphRef::new(self);

        while let Some(ef) = queue.pop() {
            if seen.contains(&ef) {
                continue;
            }
            seen.insert(ef);
            tracing::debug!("Exploring from {}", ef.current());
            let edges_blocking = blocking_map.get_edges_blocking(ef.current(), repacker);
            for edge in edges_blocking.iter() {
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
                                if let Some(source) = ef.connect()
                                    && source != rp.into()
                                {
                                    graph.add_edge(&vec![source].into(), &vec![rp.into()].into());
                                }
                            }
                        }
                    }
                }
                for node in edge.blocked_by_nodes(repacker) {
                    queue.push(ef.extend(node.into()));
                }
            }
        }
        graph
    }

    pub(crate) fn frozen_graph(&self) -> FrozenGraphRef<'_, 'tcx> {
        FrozenGraphRef::new(self)
    }

    pub(crate) fn is_acyclic(&self, repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        self.frozen_graph().is_acyclic(repacker)
    }

    pub(crate) fn abstraction_edge_kinds<'slf>(
        &'slf self,
    ) -> impl Iterator<Item = &'slf AbstractionType<'tcx>> + 'slf {
        self.edges().filter_map(|edge| match edge.kind {
            BorrowPCGEdgeKind::Abstraction(abstraction) => Some(abstraction),
            _ => None,
        })
    }

    pub(crate) fn abstraction_edges<'slf>(
        &'slf self,
    ) -> impl Iterator<Item = Conditioned<&'slf AbstractionType<'tcx>>> + 'slf {
        self.edges().filter_map(|edge| match edge.kind {
            BorrowPCGEdgeKind::Abstraction(abstraction) => Some(Conditioned {
                conditions: edge.conditions().clone(),
                value: abstraction,
            }),
            _ => None,
        })
    }

    pub(crate) fn borrows(&self) -> impl Iterator<Item = Conditioned<BorrowEdge<'tcx>>> + '_ {
        self.edges().filter_map(|edge| match &edge.kind() {
            BorrowPCGEdgeKind::Borrow(reborrow) => Some(Conditioned {
                conditions: edge.conditions().clone(),
                value: reborrow.clone(),
            }),
            _ => None,
        })
    }

    /// All edges that are not blocked by any other edge The argument
    /// `blocking_map` can be provided to use a shared cache for computation
    /// of blocking calculations. The argument should be used if this function
    /// is to be called multiple times on the same graph.
    pub(crate) fn is_leaf_edge<'graph, 'mir>(
        &'graph self,
        edge: &impl BorrowPCGEdgeLike<'tcx>,
        repacker: PlaceRepacker<'mir, 'tcx>,
        mut blocking_map: Option<&FrozenGraphRef<'graph, 'tcx>>,
    ) -> bool {
        let mut has_edge_blocking = |p: PCGNode<'tcx>| {
            if let Some(blocking_map) = blocking_map.as_mut() {
                blocking_map.has_edge_blocking(p, repacker)
            } else {
                self.has_edge_blocking(p, repacker)
            }
        };
        for n in edge.blocked_by_nodes(repacker) {
            if has_edge_blocking(n.into()) {
                return false;
            }
        }
        true
    }

    pub(crate) fn leaf_edges_set<'slf, 'mir>(
        &'slf self,
        repacker: PlaceRepacker<'mir, 'tcx>,
        frozen_graph: Option<&FrozenGraphRef<'slf, 'tcx>>,
    ) -> FxHashSet<BorrowPCGEdgeRef<'tcx, 'slf>> {
        let fg = match frozen_graph {
            Some(fg) => fg,
            None => &self.frozen_graph(),
        };
        self.edges()
            .filter(move |edge| self.is_leaf_edge(edge, repacker, Some(fg)))
            .collect()
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

    pub(crate) fn roots(&self, repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<PCGNode<'tcx>> {
        let roots: FxHashSet<PCGNode<'tcx>> = self
            .nodes(repacker)
            .into_iter()
            .filter(|node| self.is_root(*node, repacker))
            .collect();
        roots
    }

    /// Returns true iff any edge in the graph blocks `blocked_node`
    ///
    /// Complexity: O(E)
    ///
    /// If you need to call this function multiple times, you can get better
    /// performance using [`FrozenGraphRef`], (c.f.
    /// [`BorrowsGraph::edges_blocking_map`]).
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
        match node.into().as_local_node() {
            Some(node) => match node {
                PCGNode::Place(place) if place.is_owned(repacker) => true,
                _ => !self.has_edge_blocked_by(node, repacker),
            },
            None => true,
        }
    }

    pub(crate) fn has_edge_blocked_by(
        &self,
        node: LocalNode<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        self.edges().any(|edge| edge.is_blocked_by(node, repacker))
    }

    pub(crate) fn num_edges(&self) -> usize {
        self.edges.len()
    }

    pub(crate) fn edges_blocked_by<'graph, 'mir: 'graph>(
        &'graph self,
        node: LocalNode<'tcx>,
        repacker: PlaceRepacker<'mir, 'tcx>,
    ) -> impl Iterator<Item = BorrowPCGEdgeRef<'tcx, 'graph>> {
        self.edges()
            .filter(move |edge| edge.blocked_by_nodes(repacker).contains(&node))
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
        other_block: BasicBlock,
        repacker: PlaceRepacker<'_, 'tcx>,
        borrow_checker: &T,
    ) {
        let is_loop_abstraction_for_this_block = |edge: BorrowPCGEdgeRef<'_, '_>| {
            if let BorrowPCGEdgeKind::Abstraction(abstraction_edge) = &edge.kind() {
                if let AbstractionType::Loop(loop_abstraction) = &abstraction_edge {
                    return loop_abstraction.location().block == self_block;
                }
            }
            false
        };

        let self_coupling_graph =
            self.construct_coupling_graph(borrow_checker, repacker, other_block);
        let other_coupling_graph =
            other.construct_coupling_graph(borrow_checker, repacker, other_block);

        if coupling_imgcat_debug() {
            self_coupling_graph
                .render_with_imgcat(&format!("self coupling graph: {:?}", self_block));
            other_coupling_graph
                .render_with_imgcat(&format!("other coupling graph: {:?}", other_block));
        }

        let mut result = self_coupling_graph;
        result.merge(&other_coupling_graph);
        if coupling_imgcat_debug() {
            result.render_with_imgcat("merged coupling graph");
        }

        // Collect existing loop abstraction edges at this block
        let existing_edges: FxHashSet<_> = self
            .edges()
            .filter(|edge| is_loop_abstraction_for_this_block(*edge))
            .map(|edge| edge.to_owned_edge())
            .collect();

        // Borrow PCG edges originally going through individual region projection
        // nodes should be moved to the corresponding coupled nodes.
        // TODO: Make sure `changed` is set correctly.
        for endpoint in result.endpoints() {
            let rps: Vec<RegionProjection<'tcx>> = endpoint
                .iter()
                .flat_map(|node| (*node).try_into())
                .collect::<Vec<_>>();

            let local_rps: Vec<LocalNode<'tcx>> = rps
                .iter()
                .flat_map(|rp| rp.try_to_local_node())
                .collect::<Vec<_>>();

            let edges_to_move = local_rps
                .iter()
                .flat_map(|p| {
                    self.edges_blocked_by((*p).into(), repacker)
                        .into_iter()
                        .chain(other.edges_blocked_by((*p).into(), repacker))
                        .map(|edge| edge.to_owned_edge())
                })
                .unique()
                .collect::<Vec<_>>();

            let in_rps = |p: PCGNode<'tcx>| rps.iter().any(|rp| (*rp).to_pcg_node() == p);
            for edge in edges_to_move {
                if is_loop_abstraction_for_this_block(edge.as_ref()) {
                    continue;
                }
                for node in edge.blocked_nodes(repacker) {
                    // If this blocked node is in the endpoint, no edge should
                    // be added (otherwise it would just connect the endpoint to
                    // itself)
                    if in_rps(node) {
                        break;
                    }

                    // This node is not in the endpoint, so we create a corresponding
                    // region projection member edge.
                    let new_edge_kind =
                        BorrowPCGEdgeKind::RegionProjectionMember(RegionProjectionMember::new(
                            smallvec![node],
                            rps.clone()
                                .into_iter()
                                .map(|rp| rp.try_into().unwrap())
                                .collect::<RegionProjectionMemberOutputs<'tcx>>(),
                            RegionProjectionMemberKind::Todo,
                        ));
                    self.insert(BorrowPCGEdge::new(new_edge_kind, edge.conditions().clone()));
                }
                self.remove(&edge);
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

            if !existing_edges.contains(&abstraction) {
                self.insert(abstraction);
            }
        }

        // Edges that only connect nodes within the region abstraction (but are
        // not the abstraction edge itself), should be removed
        let encapsulated_edges = self
            .edges()
            .map(|edge| edge.to_owned_edge())
            .filter(|edge| {
                if let BorrowPCGEdgeKind::Abstraction(AbstractionType::Loop(loop_abstraction)) =
                    edge.kind()
                {
                    if loop_abstraction.block == self_block {
                        return false;
                    }
                }
                self.is_encapsulated_by_abstraction(edge, repacker)
            })
            .collect::<Vec<_>>();

        for edge in encapsulated_edges {
            self.remove(&edge);
        }

        // The process may result interior (old) places now being roots in the
        // graph. These should be removed.
        for root in self.roots(repacker) {
            if root.is_old() {
                for edge in self
                    .edges_blocking(root, repacker)
                    .map(|edge| edge.to_owned_edge())
                    .collect::<Vec<_>>()
                {
                    self.remove(&edge);
                }
            }
        }
    }

    /// Returns true iff `edge` connects two nodes within an abstraction edge
    fn is_encapsulated_by_abstraction(
        &self,
        edge: &impl BorrowPCGEdgeLike<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        'outer: for abstraction in self.abstraction_edge_kinds() {
            for blocked in edge.blocked_nodes(repacker) {
                if !abstraction.blocks_node(blocked, repacker) {
                    continue 'outer;
                }
            }
            for blocked_by in edge.blocked_by_nodes(repacker) {
                if !abstraction.is_blocked_by(blocked_by, repacker) {
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
        // For performance reasons we don't check validity here.
        // if validity_checks_enabled() {
        //     pcg_validity_assert!(other.is_valid(repacker), "Other graph is invalid");
        // }
        #[allow(unused)]
        let old_self = self.clone();

        #[allow(unused)]
        let other_frozen = other.frozen_graph();

        if borrows_imgcat_debug() {
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

        let is_back_edge = repacker.is_back_edge(other_block, self_block);
        let span = span!(Level::INFO, "join", is_back_edge);
        let _guard = span.enter();

        if repacker.is_back_edge(other_block, self_block) {
            self.join_loop(other, self_block, other_block, repacker, bc);
            let result = *self != old_self;
            if borrows_imgcat_debug() {
                if let Ok(dot_graph) = generate_borrows_dot_graph(repacker, self) {
                    DotGraph::render_with_imgcat(
                        &dot_graph,
                        &format!("After join (loop, changed={:?}):", result),
                    )
                    .unwrap_or_else(|e| {
                        eprintln!("Error rendering self graph: {}", e);
                    });
                    if result {
                        eprintln!("{}", old_self.fmt_diff(self, repacker))
                    }
                }
            }
            // For performance reasons we don't check validity here.
            // if validity_checks_enabled() {
            //     assert!(self.is_valid(repacker), "Graph became invalid after join");
            // }
            return result;
        }
        for other_edge in other.edges() {
            self.insert(other_edge.to_owned_edge());
        }
        for edge in self
            .edges()
            .map(|edge| edge.to_owned_edge())
            .collect::<Vec<_>>()
        {
            if let BorrowPCGEdgeKind::Abstraction(_) = edge.kind() {
                continue;
            }
            if self.is_encapsulated_by_abstraction(&edge, repacker) {
                self.remove(&edge);
            }
        }

        let changed = old_self != *self;

        if borrows_imgcat_debug() {
            if let Ok(dot_graph) = generate_borrows_dot_graph(repacker, self) {
                DotGraph::render_with_imgcat(
                    &dot_graph,
                    &format!("After join: (changed={:?})", changed),
                )
                .unwrap_or_else(|e| {
                    eprintln!("Error rendering self graph: {}", e);
                });
                if changed {
                    eprintln!("{}", old_self.fmt_diff(self, repacker))
                }
            }
        }

        // For performance reasons we only check validity here if we are also producing debug graphs
        if validity_checks_enabled() && borrows_imgcat_debug() && !self.is_valid(repacker) {
            if let Ok(dot_graph) = generate_borrows_dot_graph(repacker, self) {
                DotGraph::render_with_imgcat(&dot_graph, "Invalid self graph").unwrap_or_else(
                    |e| {
                        eprintln!("Error rendering self graph: {}", e);
                    },
                );
            }
            if let Ok(dot_graph) = generate_borrows_dot_graph(repacker, &old_self) {
                DotGraph::render_with_imgcat(&dot_graph, "Old self graph").unwrap_or_else(|e| {
                    eprintln!("Error rendering old self graph: {}", e);
                });
            }
            if let Ok(dot_graph) = generate_borrows_dot_graph(repacker, other) {
                DotGraph::render_with_imgcat(&dot_graph, "Other graph").unwrap_or_else(|e| {
                    eprintln!("Error rendering other graph: {}", e);
                });
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

    pub(crate) fn insert(&mut self, edge: BorrowPCGEdge<'tcx>) -> bool {
        if let Some(conditions) = self.edges.get_mut(edge.kind()) {
            return conditions.join(&edge.conditions);
        } else {
            self.edges.insert(edge.kind, edge.conditions);
            self.cached_leaf_nodes.borrow_mut().take();
            true
        }
    }

    pub(crate) fn edges_blocking<'slf, 'mir: 'slf>(
        &'slf self,
        node: BlockedNode<'tcx>,
        repacker: PlaceRepacker<'mir, 'tcx>,
    ) -> impl Iterator<Item = BorrowPCGEdgeRef<'tcx, 'slf>> + 'slf {
        self.edges()
            .filter(move |edge| edge.blocks_node(node, repacker))
    }

    pub(crate) fn edges_blocking_set<'slf, 'mir>(
        &'slf self,
        node: BlockedNode<'tcx>,
        repacker: PlaceRepacker<'mir, 'tcx>,
    ) -> FxHashSet<BorrowPCGEdgeRef<'tcx, 'slf>> {
        self.edges()
            .filter(move |edge| edge.blocks_node(node, repacker))
            .collect()
    }

    pub(crate) fn remove(&mut self, edge: &impl BorrowPCGEdgeLike<'tcx>) -> bool {
        if let Some(conditions) = self.edges.get_mut(edge.kind()) {
            if conditions == edge.conditions() {
                self.edges.remove(edge.kind());
                self.cached_leaf_nodes.borrow_mut().take();
            } else {
                assert!(conditions.remove(edge.conditions()));
            }
            true
        } else {
            false
        }
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
            if validity_checks_enabled() {
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
            .map(|(kind, conditions)| {
                let mut edge = BorrowPCGEdge::new(kind, conditions);
                if f(&mut edge) {
                    changed = true;
                }
                (edge.kind, edge.conditions)
            })
            .collect();
        if changed {
            self.cached_leaf_nodes.borrow_mut().take();
        }
        changed
    }

    fn mut_edge_conditions<'slf>(
        &'slf mut self,
        mut f: impl FnMut(&mut PathConditions) -> bool,
    ) -> bool {
        let mut changed = false;
        for (_, conditions) in self.edges.iter_mut() {
            if f(conditions) {
                changed = true;
            }
        }
        changed
    }

    pub fn filter_for_path(&mut self, path: &[BasicBlock]) {
        self.edges
            .retain(|_, conditions| conditions.valid_for_path(path));
        self.cached_leaf_nodes.borrow_mut().take();
    }

    pub(crate) fn add_path_condition(&mut self, pc: PathCondition) -> bool {
        self.mut_edge_conditions(|conditions| conditions.insert(pc.clone()))
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

pub(crate) struct FrozenGraphRef<'graph, 'tcx> {
    graph: &'graph BorrowsGraph<'tcx>,
    nodes_cache: RefCell<Option<FxHashSet<PCGNode<'tcx>>>>,
    edges_blocking_cache:
        RefCell<HashMap<PCGNode<'tcx>, FxHashSet<BorrowPCGEdgeRef<'tcx, 'graph>>>>,
    edges_blocked_by_cache:
        RefCell<HashMap<LocalNode<'tcx>, FxHashSet<BorrowPCGEdgeRef<'tcx, 'graph>>>>,
    leaf_edges_cache: RefCell<Option<FxHashSet<BorrowPCGEdgeRef<'tcx, 'graph>>>>,
    roots_cache: RefCell<Option<FxHashSet<PCGNode<'tcx>>>>,
}

impl<'graph, 'tcx> FrozenGraphRef<'graph, 'tcx> {
    pub(crate) fn new(graph: &'graph BorrowsGraph<'tcx>) -> Self {
        Self {
            graph,
            nodes_cache: RefCell::new(None),
            edges_blocking_cache: RefCell::new(HashMap::new()),
            edges_blocked_by_cache: RefCell::new(HashMap::new()),
            leaf_edges_cache: RefCell::new(None),
            roots_cache: RefCell::new(None),
        }
    }

    pub(crate) fn contains(&self, node: PCGNode<'tcx>, repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        self.nodes(repacker).contains(&node)
    }

    pub(crate) fn nodes<'slf>(
        &'slf self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Ref<'slf, FxHashSet<PCGNode<'tcx>>> {
        {
            let nodes = self.nodes_cache.borrow();
            if nodes.is_some() {
                return Ref::map(nodes, |o| o.as_ref().unwrap());
            }
        }
        let nodes = self.graph.nodes(repacker);
        self.nodes_cache.replace(Some(nodes));
        Ref::map(self.nodes_cache.borrow(), |o| o.as_ref().unwrap())
    }

    pub(crate) fn roots<'slf>(
        &'slf self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Ref<'slf, FxHashSet<PCGNode<'tcx>>> {
        {
            let roots = self.roots_cache.borrow();
            if roots.is_some() {
                return Ref::map(roots, |o| o.as_ref().unwrap());
            }
        }
        let roots = self.graph.roots(repacker);
        self.roots_cache.replace(Some(roots));
        Ref::map(self.roots_cache.borrow(), |o| o.as_ref().unwrap())
    }

    pub(crate) fn leaf_edges<'slf, 'mir>(
        &'slf self,
        repacker: PlaceRepacker<'mir, 'tcx>,
    ) -> FxHashSet<BorrowPCGEdgeRef<'tcx, 'graph>> {
        {
            let edges = self.leaf_edges_cache.borrow();
            if edges.is_some() {
                return edges.as_ref().unwrap().clone();
            }
        }
        let edges: FxHashSet<_> = self.graph.leaf_edges_set(repacker, Some(self));
        self.leaf_edges_cache.replace(Some(edges.clone()));
        edges
    }

    #[allow(unused)]
    pub(crate) fn get_edges_blocked_by<'mir: 'graph>(
        &mut self,
        node: LocalNode<'tcx>,
        repacker: PlaceRepacker<'mir, 'tcx>,
    ) -> &FxHashSet<BorrowPCGEdgeRef<'tcx, 'graph>> {
        self.edges_blocked_by_cache
            .get_mut()
            .entry(node)
            .or_insert_with(|| self.graph.edges_blocked_by(node, repacker).collect())
    }

    pub(crate) fn get_edges_blocking<'slf, 'mir>(
        &'slf self,
        node: PCGNode<'tcx>,
        repacker: PlaceRepacker<'mir, 'tcx>,
    ) -> FxHashSet<BorrowPCGEdgeRef<'tcx, 'graph>> {
        {
            let map = self.edges_blocking_cache.borrow();
            if map.contains_key(&node) {
                return map[&node].clone();
            }
        }
        let edges: FxHashSet<BorrowPCGEdgeRef<'tcx, 'graph>> =
            self.graph.edges_blocking_set(node, repacker);
        self.edges_blocking_cache
            .borrow_mut()
            .insert(node, edges.clone());
        edges
    }

    pub(crate) fn has_edge_blocking(
        &self,
        node: PCGNode<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        {
            let map = self.edges_blocking_cache.borrow();
            if map.contains_key(&node) {
                return !map[&node].is_empty();
            }
        }
        let edges: FxHashSet<_> = self.graph.edges_blocking_set(node, repacker);
        let result = !edges.is_empty();
        self.edges_blocking_cache.borrow_mut().insert(node, edges);
        result
    }

    fn is_acyclic<'mir: 'graph>(&mut self, repacker: PlaceRepacker<'mir, 'tcx>) -> bool {
        // The representation of an allowed path prefix, e.g. paths
        // with this representation definitely cannot reach a feasible cycle.
        type AllowedPathPrefix<'tcx, 'graph> = Path<'tcx, 'graph>;

        let mut allowed_path_prefixes: HashSet<AllowedPathPrefix<'tcx, 'graph>> = HashSet::new();

        enum PushResult<'tcx, 'graph> {
            ExtendPath(Path<'tcx, 'graph>),
            Cycle,
            PathConditionsUnsatisfiable,
        }

        #[derive(Clone, Debug, Eq, PartialEq, Hash)]
        struct Path<'tcx, 'graph>(Vec<BorrowPCGEdgeRef<'tcx, 'graph>>);
        impl<'tcx, 'graph> Path<'tcx, 'graph> {
            /// Checks if the path is actually feasible, i.e. there is an
            /// execution path of the program such that the path conditions of
            /// each edge are satisfied.
            ///
            /// Note that this check is very conservative right now (basically
            /// only checking some obvious cases)
            fn is_feasible(&self, repacker: PlaceRepacker<'_, 'tcx>) -> bool {
                let leaf_blocks = repacker
                    .body()
                    .basic_blocks
                    .iter_enumerated()
                    .filter(|(_, bb)| matches!(bb.terminator().edges(), TerminatorEdges::None))
                    .map(|(idx, _)| idx)
                    .collect::<Vec<_>>();

                // Maps leaf blocks `be` to a block `bs`, where the path feasibility
                // requires an edge `bs` -> `be`. If `bs` is not unique for some
                // `be`, then the path is definitely not feasible.
                let mut end_blocks_map = HashMap::new();
                for edge in self.0.iter() {
                    match edge.conditions() {
                        PathConditions::Paths(pcgraph) => {
                            for block in leaf_blocks.iter() {
                                let edges = pcgraph.edges_to(*block);
                                if edges.len() == 1 {
                                    let from_block = edges.iter().next().unwrap().from;
                                    if let Some(bs) = end_blocks_map.insert(block, from_block) {
                                        if bs != from_block {
                                            return false;
                                        }
                                    }
                                }
                            }
                        }
                        PathConditions::AtBlock(_) => {}
                    }
                }
                return true;
            }

            fn try_push(
                mut self,
                edge: BorrowPCGEdgeRef<'tcx, 'graph>,
                repacker: PlaceRepacker<'_, 'tcx>,
            ) -> PushResult<'tcx, 'graph> {
                if let Some(_) = self.0.iter().position(|e| *e == edge) {
                    PushResult::Cycle
                } else {
                    self.0.push(edge);
                    if self.is_feasible(repacker) {
                        PushResult::ExtendPath(self)
                    } else {
                        PushResult::PathConditionsUnsatisfiable
                    }
                }
            }

            fn last(&self) -> BorrowPCGEdgeRef<'tcx, 'graph> {
                *self.0.last().unwrap()
            }

            fn new(edge: BorrowPCGEdgeRef<'tcx, 'graph>) -> Self {
                Self(vec![edge])
            }

            fn path_prefix_repr(&self) -> AllowedPathPrefix<'tcx, 'graph> {
                self.clone()
            }

            fn leads_to_feasible_cycle<'mir: 'graph>(
                &self,
                graph: &FrozenGraphRef<'graph, 'tcx>,
                repacker: PlaceRepacker<'mir, 'tcx>,
                prefixes: &mut HashSet<AllowedPathPrefix<'tcx, 'graph>>,
            ) -> bool {
                let path_prefix_repr = self.path_prefix_repr();
                if prefixes.contains(&path_prefix_repr) {
                    return false;
                }
                let curr = self.last();
                let blocking_edges = curr
                    .blocked_by_nodes(repacker)
                    .into_iter()
                    .flat_map(|node| {
                        graph
                            .get_edges_blocking(node.into(), repacker)
                            .iter()
                            .copied()
                            .collect::<Vec<_>>()
                    })
                    .unique();
                for edge in blocking_edges {
                    match self.clone().try_push(edge, repacker) {
                        PushResult::Cycle => {
                            return true;
                        }
                        PushResult::ExtendPath(next_path) => {
                            next_path.leads_to_feasible_cycle(graph, repacker, prefixes);
                        }
                        PushResult::PathConditionsUnsatisfiable => {}
                    }
                }
                prefixes.insert(path_prefix_repr);
                false
            }
        }

        for root in self.roots(repacker).iter() {
            for edge in self.get_edges_blocking((*root).into(), repacker).iter() {
                if Path::new(*edge).leads_to_feasible_cycle(
                    self,
                    repacker,
                    &mut allowed_path_prefixes,
                ) {
                    return false;
                }
            }
        }

        return true;
    }
}
