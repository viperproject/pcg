pub mod aliases;
pub mod frozen;
pub mod join;
pub(crate) mod materialize;
mod mutate;

use std::collections::HashSet;

use crate::{
    borrow_pcg::coupling_graph_constructor::AbstractionGraph,
    combined_pcs::PCGNode,
    rustc_interface::{
        data_structures::fx::{FxHashMap, FxHashSet},
        middle::mir::{self, BasicBlock},
    },
    utils::{
        display::{DebugLines, DisplayWithRepacker},
        maybe_old::MaybeOldPlace,
        validity::HasValidityCheck,
    },
};
use frozen::{CachedLeafEdges, FrozenGraphRef};
use serde_json::json;

use super::{
    borrow_pcg_edge::{BlockedNode, BorrowPCGEdge, BorrowPCGEdgeLike, BorrowPCGEdgeRef, LocalNode},
    coupling_graph_constructor::{
        BorrowCheckerInterface, CGNode, AbstractionGraphConstructor,
    },
    edge::borrow::LocalBorrow,
    edge_data::EdgeData,
    path_condition::PathConditions,
};
use crate::borrow_pcg::edge::abstraction::AbstractionType;
use crate::borrow_pcg::edge::borrow::BorrowEdge;
use crate::borrow_pcg::edge::kind::BorrowPCGEdgeKind;
use crate::utils::json::ToJsonWithRepacker;
use crate::utils::{env_feature_enabled, PlaceRepacker};

#[derive(Clone, Debug)]
pub struct BorrowsGraph<'tcx> {
    edges: FxHashMap<BorrowPCGEdgeKind<'tcx>, PathConditions>,
}

impl<'tcx> DebugLines<PlaceRepacker<'_, 'tcx>> for BorrowsGraph<'tcx> {
    fn debug_lines(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Vec<String> {
        self.edges()
            .map(|edge| edge.to_short_string(repacker).to_string())
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

impl Eq for BorrowsGraph<'_> {}

impl PartialEq for BorrowsGraph<'_> {
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
    pub(crate) fn borrow_created_at(&self, location: mir::Location) -> Option<&LocalBorrow<'tcx>> {
        for edge in self.edges() {
            if let BorrowPCGEdgeKind::Borrow(BorrowEdge::Local(borrow)) = edge.kind {
                if borrow.reserve_location() == location {
                    return Some(borrow);
                }
            }
        }
        None
    }

    pub(crate) fn common_edges(&self, other: &Self) -> FxHashSet<BorrowPCGEdgeKind<'tcx>> {
        let mut common_edges = FxHashSet::default();
        for (edge_kind, _) in self.edges.iter() {
            if other.edges.contains_key(edge_kind) {
                common_edges.insert(edge_kind.clone());
            }
        }
        common_edges
    }

    pub(crate) fn has_function_call_abstraction_at(&self, location: mir::Location) -> bool {
        for edge in self.edges() {
            if let BorrowPCGEdgeKind::Abstraction(abstraction) = edge.kind() {
                if abstraction.is_function_call() && abstraction.location() == location {
                    return true;
                }
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
                    .as_blocking_node(repacker)
                    .map(|blocking| edge.blocked_by_nodes(repacker).contains(&blocking))
                    .unwrap_or(false)
        })
    }

    pub(crate) fn new() -> Self {
        Self {
            edges: FxHashMap::default(),
        }
    }

    pub fn edges<'slf>(&'slf self) -> impl Iterator<Item = BorrowPCGEdgeRef<'tcx, 'slf>> + 'slf {
        self.edges
            .iter()
            .map(|(kind, conditions)| BorrowPCGEdgeRef { kind, conditions })
    }

    pub(crate) fn base_rp_graph(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> AbstractionGraph<'tcx> {
        let mut graph: AbstractionGraph<'tcx> = AbstractionGraph::new();
        #[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
        struct ExploreFrom<'tcx> {
            current: PCGNode<'tcx>,
            connect: Option<CGNode<'tcx>>,
        }

        impl<'tcx> ExploreFrom<'tcx> {
            pub fn new(current: PCGNode<'tcx>, repacker: PlaceRepacker<'_, 'tcx>) -> Self {
                Self {
                    current,
                    connect: current.as_cg_node(repacker),
                }
            }

            pub fn connect(&self) -> Option<CGNode<'tcx>> {
                self.connect
            }

            pub fn current(&self) -> PCGNode<'tcx> {
                self.current
            }

            pub fn extend(&self, node: PCGNode<'tcx>, repacker: PlaceRepacker<'_, 'tcx>) -> Self {
                Self {
                    current: node,
                    connect: node.as_cg_node(repacker).or(self.connect),
                }
            }
        }

        impl std::fmt::Display for ExploreFrom<'_> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(
                    f,
                    "Current: {}, Connect: {}",
                    self.current,
                    match self.connect {
                        Some(cg_node) => format!("{:?}", cg_node),
                        None => "None".to_string(),
                    }
                )
            }
        }

        let mut seen = HashSet::new();
        let frozen_graph = FrozenGraphRef::new(self);

        let mut queue = vec![];
        for node in frozen_graph.roots(repacker).iter() {
            tracing::debug!("Adding root node to queue: {:?}", node);
            queue.push(ExploreFrom::new(*node, repacker));
        }

        while let Some(ef) = queue.pop() {
            if seen.contains(&ef) {
                continue;
            }
            seen.insert(ef);
            let edges_blocking = frozen_graph.get_edges_blocking(ef.current(), repacker);
            for edge in edges_blocking {
                match edge.kind() {
                    BorrowPCGEdgeKind::Abstraction(abstraction_edge) => {
                        let inputs = abstraction_edge
                            .inputs()
                            .into_iter()
                            .collect::<Vec<_>>()
                            .into();
                        let outputs = abstraction_edge
                            .outputs()
                            .into_iter()
                            .map(|node| node.into())
                            .collect::<Vec<_>>()
                            .into();
                        graph.add_edge(
                            &inputs,
                            &outputs,
                            std::iter::once(edge.kind().to_owned()).collect(),
                            repacker,
                        );
                    }
                    BorrowPCGEdgeKind::BorrowPCGExpansion(e)
                        if e.is_owned_expansion(repacker)
                            && ef
                                .current()
                                .as_maybe_old_place()
                                .is_some_and(|p| p.is_owned(repacker)) =>
                    {
                        continue
                    }
                    _ => {
                        for node in edge.blocked_by_nodes(repacker) {
                            if let LocalNode::RegionProjection(rp) = node {
                                if let Some(source) = ef.connect()
                                    && source != rp.into()
                                {
                                    graph.add_edge(
                                        &vec![source].into(),
                                        &vec![rp.into()].into(),
                                        std::iter::once(edge.kind().to_owned()).collect(),
                                        repacker,
                                    );
                                }
                            }
                        }
                    }
                }
                for node in edge.blocked_by_nodes(repacker) {
                    queue.push(ef.extend(node.into(), repacker));
                }
            }
        }
        graph
    }

    pub fn frozen_graph(&self) -> FrozenGraphRef<'_, 'tcx> {
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
    pub(crate) fn is_leaf_edge<'graph, 'mir: 'graph>(
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

    pub(crate) fn leaf_edges_set<'slf, 'mir: 'slf>(
        &'slf self,
        repacker: PlaceRepacker<'mir, 'tcx>,
        frozen_graph: Option<&FrozenGraphRef<'slf, 'tcx>>,
    ) -> CachedLeafEdges<'slf, 'tcx> {
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
        match node.into().as_local_node(repacker) {
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

    pub fn edges_blocked_by<'graph, 'mir: 'graph>(
        &'graph self,
        node: LocalNode<'tcx>,
        repacker: PlaceRepacker<'mir, 'tcx>,
    ) -> impl Iterator<Item = BorrowPCGEdgeRef<'tcx, 'graph>> {
        self.edges()
            .filter(move |edge| edge.blocked_by_nodes(repacker).contains(&node))
    }

    #[tracing::instrument(skip(self, borrow_checker, repacker))]
    fn construct_region_projection_abstraction<'mir>(
        &self,
        borrow_checker: &dyn BorrowCheckerInterface<'mir, 'tcx>,
        repacker: PlaceRepacker<'mir, 'tcx>,
        block: BasicBlock,
    ) -> AbstractionGraph<'tcx> {
        let constructor = AbstractionGraphConstructor::new(repacker, block);
        constructor.construct_abstraction_graph(self, borrow_checker)
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

    pub(crate) fn rename_place(
        &mut self,
        old: MaybeOldPlace<'tcx>,
        new: MaybeOldPlace<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        self.mut_pcs_elems(
            |thing| {
                if *thing == old {
                    *thing = new;
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
            conditions.join(&edge.conditions)
        } else {
            self.edges.insert(edge.kind, edge.conditions);
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

    pub(crate) fn edges_blocking_set<'slf, 'mir: 'slf>(
        &'slf self,
        node: BlockedNode<'tcx>,
        repacker: PlaceRepacker<'mir, 'tcx>,
    ) -> Vec<BorrowPCGEdgeRef<'tcx, 'slf>> {
        self.edges_blocking(node, repacker).collect()
    }

    pub(crate) fn remove(&mut self, edge: &impl BorrowPCGEdgeLike<'tcx>) -> bool {
        if let Some(conditions) = self.edges.get_mut(edge.kind()) {
            if conditions == edge.conditions() {
                self.edges.remove(edge.kind());
            } else {
                assert!(conditions.remove(edge.conditions()));
            }
            true
        } else {
            false
        }
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
