pub mod aliases;
pub mod frozen;
pub mod join;
pub(crate) mod materialize;
mod mutate;

use crate::{
    borrow_pcg::{
        abstraction::node::AbstractionGraphNode, abstraction_graph_constructor::AbstractionGraph,
        util::ExploreFrom,
    },
    pcg::PCGNode,
    rustc_interface::{
        data_structures::fx::{FxHashMap, FxHashSet},
        middle::mir::{self},
    },
    utils::{
        display::{DebugLines, DisplayWithCompilerCtxt},
        validity::HasValidityCheck,
        BORROWS_DEBUG_IMGCAT, COUPLING_DEBUG_IMGCAT,
    },
};
use frozen::{CachedBlockingEdges, CachedLeafEdges, FrozenGraphRef};
use itertools::Itertools;
use serde_json::json;

use super::{
    borrow_pcg_edge::{BlockedNode, BorrowPCGEdgeRef, BorrowPcgEdge, BorrowPcgEdgeLike, LocalNode},
    edge::borrow::LocalBorrow,
    edge_data::EdgeData,
    path_condition::PathConditions,
};
use crate::borrow_pcg::edge::abstraction::AbstractionType;
use crate::borrow_pcg::edge::borrow::BorrowEdge;
use crate::borrow_pcg::edge::kind::BorrowPcgEdgeKind;
use crate::utils::json::ToJsonWithCompilerCtxt;
use crate::utils::CompilerCtxt;

#[derive(Clone, Debug, Default)]
pub struct BorrowsGraph<'tcx> {
    edges: FxHashMap<BorrowPcgEdgeKind<'tcx>, PathConditions>,
}

impl<'tcx> DebugLines<CompilerCtxt<'_, 'tcx>> for BorrowsGraph<'tcx> {
    fn debug_lines(&self, repacker: CompilerCtxt<'_, 'tcx>) -> Vec<String> {
        self.edges()
            .map(|edge| edge.to_short_string(repacker).to_string())
            .sorted()
            .collect()
    }
}

impl<'tcx> HasValidityCheck<'tcx> for BorrowsGraph<'tcx> {
    #[allow(unused)]
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        let nodes = self.nodes(ctxt);
        // TODO
        // for node in nodes.iter() {
        //     if let PCGNode::RegionProjection(rp) = node
        //         && rp.is_placeholder()
        //     {
        //         if nodes
        //             .iter()
        //             .any(|n| matches!(n, PCGNode::RegionProjection(rp2) if rp.base == rp2.base && rp.region_idx == rp2.region_idx && rp2.label().is_none())) {
        //                 return Err(format!(
        //                     "Placeholder region projection {} is not unique",
        //                     rp.to_short_string(ctxt)
        //                 ));
        //             }
        //     }
        // }
        for edge in self.edges() {
            edge.check_validity(ctxt)?;
        }
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
    *COUPLING_DEBUG_IMGCAT
}

pub(crate) fn borrows_imgcat_debug() -> bool {
    *BORROWS_DEBUG_IMGCAT
}

impl<'tcx> BorrowsGraph<'tcx> {
    pub(crate) fn borrow_created_at(&self, location: mir::Location) -> Option<&LocalBorrow<'tcx>> {
        for edge in self.edges() {
            if let BorrowPcgEdgeKind::Borrow(BorrowEdge::Local(borrow)) = edge.kind
                && borrow.reserve_location() == location
            {
                return Some(borrow);
            }
        }
        None
    }

    pub(crate) fn common_edges(&self, other: &Self) -> FxHashSet<BorrowPcgEdgeKind<'tcx>> {
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
            if let BorrowPcgEdgeKind::Abstraction(abstraction) = edge.kind()
                && abstraction.is_function_call()
                && abstraction.location() == location
            {
                return true;
            }
        }
        false
    }

    pub(crate) fn redirect_edge(
        &mut self,
        mut edge: BorrowPcgEdgeKind<'tcx>,
        from: LocalNode<'tcx>,
        to: LocalNode<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) {
        let conditions = self.edges.remove(&edge).unwrap();
        if edge.redirect(from, to, ctxt) {
            self.insert(BorrowPcgEdge::new(edge, conditions), ctxt);
        }
    }

    pub(crate) fn contains<T: Into<PCGNode<'tcx>>>(
        &self,
        node: T,
        repacker: CompilerCtxt<'_, 'tcx>,
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

    pub(crate) fn into_edges(self) -> impl Iterator<Item = BorrowPcgEdge<'tcx>> {
        self.edges
            .into_iter()
            .map(|(kind, conditions)| BorrowPcgEdge { kind, conditions })
    }

    pub fn edges<'slf>(&'slf self) -> impl Iterator<Item = BorrowPCGEdgeRef<'tcx, 'slf>> + 'slf {
        self.edges
            .iter()
            .map(|(kind, conditions)| BorrowPCGEdgeRef { kind, conditions })
    }

    pub(crate) fn base_abstraction_graph<'graph, 'mir: 'graph>(
        &'graph self,
        block: mir::BasicBlock,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> AbstractionGraph<'tcx, 'graph> {
        let mut graph: AbstractionGraph<'tcx, 'graph> = AbstractionGraph::new();

        let frozen_graph = FrozenGraphRef::new(self);

        tracing::debug!(
            "Constructing abstraction graph for graph with {} edges",
            self.num_edges()
        );

        let mut queue = vec![];
        for node in frozen_graph.roots(ctxt).iter() {
            tracing::debug!("Adding root node to queue: {:?}", node);
            queue.push(ExploreFrom::new(
                *node,
                node.as_abstraction_graph_node(block, ctxt),
            ));
        }

        let mut seen = FxHashSet::default();

        let mut iteration = 0;

        while let Some(ef) = queue.pop() {
            if seen.contains(&ef) {
                continue;
            }
            seen.insert(ef);
            iteration += 1;
            if iteration % 100000 == 0 {
                tracing::info!("Iteration {iteration}",);
            }
            let edges_blocking: CachedBlockingEdges<'graph, 'tcx> =
                frozen_graph.get_edges_blocking(ef.current(), ctxt);
            for edge in edges_blocking {
                match edge.kind() {
                    BorrowPcgEdgeKind::Abstraction(abstraction_edge) => {
                        let inputs = abstraction_edge
                            .inputs()
                            .into_iter()
                            .map(|node| AbstractionGraphNode::from_pcg_node(node, block, ctxt))
                            .collect::<Vec<_>>()
                            .into();
                        let outputs = abstraction_edge
                            .outputs()
                            .into_iter()
                            .map(|node| {
                                AbstractionGraphNode::from_pcg_node(node.into(), block, ctxt)
                            })
                            .collect::<Vec<_>>()
                            .into();
                        graph.add_edge(
                            &inputs,
                            &outputs,
                            std::iter::once(edge.kind).collect(),
                            ctxt,
                        );
                    }
                    BorrowPcgEdgeKind::BorrowPcgExpansion(e)
                        if e.is_owned_expansion(ctxt)
                            && ef
                                .current()
                                .as_maybe_old_place()
                                .is_some_and(|p| p.is_owned(ctxt)) =>
                    {
                        continue
                    }
                    _ => {
                        for node in edge.blocked_by_nodes(ctxt) {
                            if let LocalNode::RegionProjection(rp) = node
                                && let Some(source) = ef.connect()
                                && source
                                    != AbstractionGraphNode::from_pcg_node(rp.into(), block, ctxt)
                            {
                                graph.add_edge(
                                    &vec![source].into(),
                                    &vec![AbstractionGraphNode::from_pcg_node(
                                        rp.into(),
                                        block,
                                        ctxt,
                                    )]
                                    .into(),
                                    std::iter::once(edge.kind).collect(),
                                    ctxt,
                                );
                            }
                        }
                    }
                }
                for node in edge.blocked_by_nodes(ctxt) {
                    let pcg_node = node.into();
                    queue.push(ExploreFrom::new(
                        pcg_node,
                        pcg_node
                            .as_abstraction_graph_node(block, ctxt)
                            .or(ef.connect()),
                    ));
                }
            }
        }
        graph
    }

    pub fn frozen_graph(&self) -> FrozenGraphRef<'_, 'tcx> {
        FrozenGraphRef::new(self)
    }

    pub(crate) fn abstraction_edge_kinds<'slf>(
        &'slf self,
    ) -> impl Iterator<Item = &'slf AbstractionType<'tcx>> + 'slf {
        self.edges().filter_map(|edge| match edge.kind {
            BorrowPcgEdgeKind::Abstraction(abstraction) => Some(abstraction),
            _ => None,
        })
    }

    pub(crate) fn abstraction_edges<'slf>(
        &'slf self,
    ) -> impl Iterator<Item = Conditioned<&'slf AbstractionType<'tcx>>> + 'slf {
        self.edges().filter_map(|edge| match edge.kind {
            BorrowPcgEdgeKind::Abstraction(abstraction) => Some(Conditioned {
                conditions: edge.conditions().clone(),
                value: abstraction,
            }),
            _ => None,
        })
    }

    /// All edges that are not blocked by any other edge The argument
    /// `blocking_map` can be provided to use a shared cache for computation
    /// of blocking calculations. The argument should be used if this function
    /// is to be called multiple times on the same graph.
    pub(crate) fn is_leaf_edge<'graph, 'mir: 'graph, 'bc: 'graph>(
        &'graph self,
        edge: &impl BorrowPcgEdgeLike<'tcx>,
        repacker: CompilerCtxt<'mir, 'tcx>,
        mut blocking_map: Option<&FrozenGraphRef<'graph, 'tcx>>,
    ) -> bool {
        let mut has_edge_blocking = |p: PCGNode<'tcx>| {
            if let Some(blocking_map) = blocking_map.as_mut() {
                blocking_map.has_edge_blocking(p, repacker)
            } else {
                !self.is_leaf(p, repacker)
            }
        };
        for n in edge.blocked_by_nodes(repacker) {
            if has_edge_blocking(n.into()) {
                return false;
            }
        }
        true
    }

    pub(crate) fn leaf_edges_set<'slf, 'mir: 'slf, 'bc: 'slf>(
        &'slf self,
        repacker: CompilerCtxt<'mir, 'tcx>,
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

    pub(crate) fn nodes<'slf>(&self, repacker: CompilerCtxt<'_, 'tcx>) -> FxHashSet<PCGNode<'tcx>> {
        self.edges()
            .flat_map(|edge| {
                edge.blocked_nodes(repacker)
                    .chain(edge.blocked_by_nodes(repacker).map(|node| node.into()))
                    .collect::<Vec<_>>()
            })
            .collect()
    }

    pub(crate) fn roots(&self, repacker: CompilerCtxt<'_, 'tcx>) -> FxHashSet<PCGNode<'tcx>> {
        let roots: FxHashSet<PCGNode<'tcx>> = self
            .nodes(repacker)
            .into_iter()
            .filter(|node| self.is_root(*node, repacker))
            .collect();
        roots
    }

    pub(crate) fn is_leaf<T: Into<BlockedNode<'tcx>>>(
        &self,
        blocked_node: T,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        let blocked_node = blocked_node.into();
        !self
            .edges()
            .any(|edge| edge.blocks_node(blocked_node, repacker))
    }

    pub(crate) fn is_root<T: Copy + Into<PCGNode<'tcx>>>(
        &self,
        node: T,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.contains(node.into(), ctxt) && match node.into().as_local_node(ctxt) {
            Some(node) => match node {
                PCGNode::Place(place) if place.is_owned(ctxt) => true,
                _ => !self.has_edge_blocked_by(node, ctxt),
            },
            None => true,
        }
    }

    pub(crate) fn has_edge_blocked_by<'slf>(
        &self,
        node: LocalNode<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.edges().any(|edge| edge.is_blocked_by(node, repacker))
    }

    pub(crate) fn num_edges(&self) -> usize {
        self.edges.len()
    }

    pub fn edges_blocked_by<'graph, 'mir: 'graph, 'bc: 'graph>(
        &'graph self,
        node: LocalNode<'tcx>,
        repacker: CompilerCtxt<'mir, 'tcx>,
    ) -> impl Iterator<Item = BorrowPCGEdgeRef<'tcx, 'graph>> + use<'tcx, 'graph, 'mir, 'bc> {
        self.edges()
            .filter(move |edge| edge.blocked_by_nodes(repacker).contains(&node))
    }

    /// Returns true iff `edge` connects two nodes within an abstraction edge
    fn is_encapsulated_by_abstraction(
        &self,
        edge: &impl BorrowPcgEdgeLike<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
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

    pub(crate) fn insert(
        &mut self,
        edge: BorrowPcgEdge<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        if let Some(conditions) = self.edges.get_mut(edge.kind()) {
            conditions.join(&edge.conditions, ctxt.body())
        } else {
            self.edges.insert(edge.kind, edge.conditions);
            true
        }
    }

    pub(crate) fn edges_blocking<'slf, 'mir: 'slf, 'bc: 'slf>(
        &'slf self,
        node: BlockedNode<'tcx>,
        repacker: CompilerCtxt<'mir, 'tcx>,
    ) -> impl Iterator<Item = BorrowPCGEdgeRef<'tcx, 'slf>> + use<'tcx, 'slf, 'mir, 'bc> {
        self.edges()
            .filter(move |edge| edge.blocks_node(node, repacker))
    }

    pub(crate) fn edges_blocking_set<'slf, 'mir: 'slf, 'bc: 'slf>(
        &'slf self,
        node: BlockedNode<'tcx>,
        repacker: CompilerCtxt<'mir, 'tcx>,
    ) -> Vec<BorrowPCGEdgeRef<'tcx, 'slf>> {
        self.edges_blocking(node, repacker).collect()
    }

    pub(crate) fn remove(&mut self, edge: &BorrowPcgEdgeKind<'tcx>) -> bool {
        self.edges.remove(edge).is_some()
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

impl<'tcx, T: ToJsonWithCompilerCtxt<'tcx>> ToJsonWithCompilerCtxt<'tcx> for Conditioned<T> {
    fn to_json(&self, repacker: CompilerCtxt<'_, 'tcx>) -> serde_json::Value {
        json!({
            "conditions": self.conditions.to_json(repacker),
            "value": self.value.to_json(repacker)
        })
    }
}
