use petgraph::algo::kosaraju_scc;
use petgraph::dot::{Config, Dot};
use petgraph::graph::{EdgeIndex, Frozen, NodeIndex};
use petgraph::visit::EdgeRef;
use petgraph::{Direction, Graph};
use smallvec::SmallVec;
use std::collections::BTreeSet;
use std::fmt;
use std::hash::Hash;

use crate::borrow_pcg::abstraction_graph_constructor::Coupled;
use crate::borrow_pcg::graph::coupling_imgcat_debug;
use crate::rustc_interface::data_structures::fx::FxHashMap;
use crate::rustc_interface::data_structures::fx::FxHashSet;
use crate::utils::display::DisplayWithCompilerCtxt;
use crate::utils::CompilerCtxt;
use crate::visualization::dot_graph::DotGraph;
use crate::{pcg_validity_assert, validity_checks_enabled};

#[derive(Clone, Debug)]
pub(crate) struct NodeData<N, E> {
    pub(crate) nodes: Coupled<N>,
    inner_edges: FxHashSet<E>,
}

impl<'tcx, N: DisplayWithCompilerCtxt<'tcx>, E> DisplayWithCompilerCtxt<'tcx> for NodeData<N, E> {
    fn to_short_string(&self, repacker: CompilerCtxt<'_, 'tcx>) -> String {
        self.nodes.to_short_string(repacker)
    }
}

impl<N: Copy + Eq, E: Hash + Eq + Clone> NodeData<N, E> {
    fn merge(&mut self, other: &NodeData<N, E>) {
        self.nodes.merge(&other.nodes);
        self.inner_edges.extend(other.inner_edges.iter().cloned());
    }
}

/// A DAG where each node is a set of elements of type `N`. Cycles are resolved
/// by merging the nodes in the cycle into a single node. The graph is always in
/// a transitively reduced form (see
/// https://en.wikipedia.org/wiki/Transitive_reduction)
#[derive(Clone)]
pub(crate) struct DisjointSetGraph<N, E> {
    inner: petgraph::Graph<NodeData<N, E>, FxHashSet<E>>,
    lookup_map: FxHashMap<N, petgraph::prelude::NodeIndex>,
}

type GetIndicesSmallVec<T> = SmallVec<[T; 4]>;

struct RequiredJoin<'a, N> {
    merge_into: NodeIndex,
    needs_insert: GetIndicesSmallVec<&'a N>,
    merge_from: GetIndicesSmallVec<NodeIndex>,
}

enum GetNodeIndicesResult<'a, N> {
    AlreadyJoined(NodeIndex),
    NoneExist,
    RequiresJoin(RequiredJoin<'a, N>),
}

pub(crate) struct JoinNodesResult {
    pub(crate) index: petgraph::prelude::NodeIndex,
    pub(crate) performed_merge: bool,
}

pub(crate) enum AddEdgeResult {
    DidNotMergeNodes,
    MergedNodes,
}

impl<
        'tcx,
        N: Copy + Ord + Clone + DisplayWithCompilerCtxt<'tcx> + Hash,
        E: Clone + Eq + Hash + DisplayWithCompilerCtxt<'tcx>,
    > DisjointSetGraph<N, E>
{
    pub(crate) fn inner(&self) -> &petgraph::Graph<NodeData<N, E>, FxHashSet<E>> {
        &self.inner
    }

    pub(crate) fn new() -> Self {
        DisjointSetGraph {
            inner: petgraph::Graph::new(),
            lookup_map: FxHashMap::default(),
        }
    }

    pub(crate) fn retain_edges<F>(&mut self, visit: F)
    where
        F: FnMut(Frozen<petgraph::Graph<NodeData<N, E>, FxHashSet<E>>>, EdgeIndex) -> bool,
    {
        self.inner.retain_edges(visit);
    }

    pub(crate) fn is_root(&self, node: &Coupled<N>) -> bool {
        self.lookup(*node.iter().next().unwrap())
            .is_some_and(|idx| {
                self.inner
                    .neighbors_directed(idx, Direction::Incoming)
                    .count()
                    == 0
            })
    }

    pub(crate) fn edges(
        &self,
    ) -> impl Iterator<Item = (Coupled<N>, Coupled<N>, FxHashSet<E>)> + '_ {
        self.inner.edge_references().map(|e| {
            let source = self.inner.node_weight(e.source()).unwrap();
            let target = self.inner.node_weight(e.target()).unwrap();
            (
                source.nodes.clone(),
                target.nodes.clone(),
                e.weight().clone(),
            )
        })
    }

    fn to_dot(&self, repacker: CompilerCtxt<'_, 'tcx>) -> String {
        let arena = bumpalo::Bump::new();
        let to_render: petgraph::Graph<&str, ()> = self.inner.clone().map(
            |_, e| {
                let node_name = format!(
                    "{}\n",
                    e.nodes.iter().fold(String::from("{"), |mut acc, x| {
                        acc.push_str(&x.to_short_string(repacker));
                        acc
                    }) + "}"
                );
                let node_name = arena.alloc(node_name);
                node_name.as_str()
            },
            |_, _| (),
        );
        let dot = format!("{:?}", Dot::with_config(&to_render, &[Config::EdgeNoLabel]));

        // Insert 'rankdir=LR;' after the first '{'
        let mut lines: Vec<&str> = dot.lines().collect();
        if let Some(index) = lines.iter().position(|&line| line.contains("{")) {
            lines.insert(index + 1, "    rankdir=LR;");
        }

        lines.join("\n")
    }

    pub(crate) fn render_with_imgcat(&self, repacker: CompilerCtxt<'_, 'tcx>, msg: &str) {
        let dot = self.to_dot(repacker);
        // let crate_name = std::env::var("CARGO_CRATE_NAME").unwrap_or_else(|_| "unknown".to_string());
        // let timestamp = std::time::SystemTime::now()
        //     .duration_since(std::time::UNIX_EPOCH)
        //     .unwrap()
        //     .as_nanos();
        // let dot_file = format!("/pcs/dotfiles/{crate_name}_{timestamp}.dot");
        // std::fs::write(&dot_file, &dot).unwrap();
        DotGraph::render_with_imgcat(&dot, msg).unwrap_or_else(|e| {
            eprintln!("Error rendering graph: {e}");
        });
    }

    pub(crate) fn insert_endpoint(
        &mut self,
        endpoint: Coupled<N>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> petgraph::prelude::NodeIndex {
        let JoinNodesResult { index, .. } = self.join_nodes(&endpoint, ctxt);
        pcg_validity_assert!(
            self.is_acyclic(),
            "Graph contains cycles after inserting endpoint"
        );
        index
    }

    fn get_node_indices<'a>(&self, nodes: &'a Coupled<N>) -> GetNodeIndicesResult<'a, N> {
        let mut merge_from: GetIndicesSmallVec<NodeIndex> = GetIndicesSmallVec::new();
        let mut needs_insert = GetIndicesSmallVec::new();
        let mut candidate_idx = None;
        for node in nodes.iter() {
            match self.lookup(*node) {
                Some(idx) => match candidate_idx {
                    Some(existing_idx) => {
                        if existing_idx != idx && !merge_from.contains(&idx) {
                            merge_from.push(idx);
                        }
                    }
                    None => {
                        candidate_idx = Some(idx);
                    }
                },
                None => {
                    needs_insert.push(node);
                }
            }
        }
        match candidate_idx {
            Some(idx) => {
                if needs_insert.is_empty() && merge_from.is_empty() {
                    GetNodeIndicesResult::AlreadyJoined(idx)
                } else {
                    GetNodeIndicesResult::RequiresJoin(RequiredJoin {
                        merge_into: idx,
                        merge_from,
                        needs_insert,
                    })
                }
            }
            None => GetNodeIndicesResult::NoneExist,
        }
    }

    /// Joins the nodes in `nodes` into a single coupled node.
    ///
    /// **IMPORTANT**: This may invalidate existing node indices
    #[must_use]
    pub(crate) fn join_nodes(
        &mut self,
        nodes: &Coupled<N>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> JoinNodesResult {
        match self.get_node_indices(nodes) {
            GetNodeIndicesResult::AlreadyJoined(node_index) => JoinNodesResult {
                index: node_index,
                performed_merge: false,
            },
            GetNodeIndicesResult::NoneExist => {
                let idx = self.inner.add_node(NodeData {
                    nodes: nodes.clone(),
                    inner_edges: FxHashSet::default(),
                });
                for node in nodes.iter() {
                    self.lookup_map.insert(*node, idx);
                }
                JoinNodesResult {
                    index: idx,
                    performed_merge: false,
                }
            }
            GetNodeIndicesResult::RequiresJoin(required_join) => {
                let node_data = &mut self
                    .inner
                    .node_weight_mut(required_join.merge_into)
                    .unwrap()
                    .nodes;
                for node in required_join.needs_insert.iter() {
                    node_data.insert(**node);
                }
                if required_join.merge_from.is_empty() {
                    return JoinNodesResult {
                        index: required_join.merge_into,
                        performed_merge: false,
                    };
                }
                for idx in required_join.merge_from.iter() {
                    // We add edges in both directions because these will be squashed into the same node
                    // when making SCCs
                    self.inner
                        .add_edge(*idx, required_join.merge_into, FxHashSet::default());
                    self.inner
                        .add_edge(required_join.merge_into, *idx, FxHashSet::default());
                }
                self.merge_sccs(ctxt);
                let (new_index, nodes) =
                    self.lookup_in_graph(*nodes.iter().next().unwrap()).unwrap();
                for node in nodes {
                    self.lookup_map.insert(node, new_index);
                }
                JoinNodesResult {
                    index: new_index,
                    performed_merge: true,
                }
            }
        }
    }

    fn lookup_in_graph(&self, node: N) -> Option<(petgraph::prelude::NodeIndex, Coupled<N>)> {
        self.inner
            .node_indices()
            .find(|idx| self.inner.node_weight(*idx).unwrap().nodes.contains(&node))
            .map(|idx| (idx, self.inner.node_weight(idx).unwrap().nodes.clone()))
    }

    pub(crate) fn lookup(&self, node: N) -> Option<petgraph::prelude::NodeIndex> {
        self.lookup_map.get(&node).cloned()
    }

    pub(crate) fn is_acyclic(&self) -> bool {
        !petgraph::algo::is_cyclic_directed(&self.inner)
    }

    /// Merges all cycles into single nodes. **IMPORTANT**: After performing this
    /// operation, the indices of the nodes may change.
    pub(crate) fn merge_sccs(&mut self, repacker: CompilerCtxt<'_, 'tcx>) {
        if self.is_acyclic() {
            return;
        }

        let sccs = kosaraju_scc(&self.inner);
        let mut result = Graph::with_capacity(sccs.len(), self.inner.edge_count());

        // Build a map from old indices to new ones.
        let mut node_map = vec![NodeIndex::end(); self.inner.node_count()];
        for comp in sccs {
            let new_nix = result.add_node(NodeData {
                nodes: Coupled::empty(),
                inner_edges: FxHashSet::default(),
            });
            for nix in comp {
                node_map[nix.index()] = new_nix;
            }
        }

        // Consume nodes and edges of the old graph and insert them into the new one.
        let (nodes, edges) = self.inner.clone().into_nodes_edges();
        for (nix, node) in nodes.into_iter().enumerate() {
            result[node_map[nix]].merge(&node.weight);
        }
        for edge in edges {
            let source = node_map[edge.source().index()];
            let target = node_map[edge.target().index()];
            if source == target {
                result[source].inner_edges.extend(edge.weight);
            } else {
                result.add_edge(source, target, edge.weight);
            }
        }
        self.inner = result;
        self.lookup_map.clear();
        for nix in self.inner.node_indices() {
            for node in self.inner.node_weight(nix).unwrap().nodes.iter() {
                self.lookup_map.insert(*node, nix);
            }
        }

        if validity_checks_enabled() && !self.is_acyclic() && coupling_imgcat_debug() {
            self.render_with_imgcat(repacker, "After merging SCCs");
        }

        pcg_validity_assert!(
            self.is_acyclic(),
            "Resulting graph contains cycles after merging SCCs"
        );
    }

    pub(crate) fn update_inner_edge(
        &mut self,
        source: NodeIndex,
        target: NodeIndex,
        weight: FxHashSet<E>,
    ) {
        self.inner.update_edge(source, target, weight);
    }

    #[must_use]
    pub(crate) fn add_edge_via_indices(
        &mut self,
        source: NodeIndex,
        target: NodeIndex,
        weight: FxHashSet<E>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> AddEdgeResult {
        assert!(source.index() < self.inner.node_count());
        assert!(target.index() < self.inner.node_count());
        if source != target {
            let edge_index = self.inner.find_edge(source, target);
            if let Some(index) = edge_index
                && let Some(current_weight) = self.inner.edge_weight_mut(index)
            {
                current_weight.extend(weight)
            } else {
                self.inner.update_edge(source, target, weight);
            }
            // If so, then there must be a cycle
            if petgraph::algo::has_path_connecting(&self.inner, target, source, None) {
                self.merge_sccs(ctxt);
                return AddEdgeResult::MergedNodes;
            }
        } else {
            self.inner
                .node_weight_mut(source)
                .unwrap()
                .inner_edges
                .extend(weight);
        }
        AddEdgeResult::DidNotMergeNodes
    }

    pub(crate) fn add_edge(
        &mut self,
        from: &Coupled<N>,
        to: &Coupled<N>,
        weight: FxHashSet<E>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) {
        pcg_validity_assert!(
            self.is_acyclic(),
            "Graph contains cycles before adding edge"
        );
        pcg_validity_assert!(
            from != to,
            "Self-loop edge {}",
            from.iter()
                .map(|x| x.to_short_string(ctxt))
                .collect::<Vec<_>>()
                .join(", ")
        );
        let JoinNodesResult {
            index: mut from_idx,
            ..
        } = self.join_nodes(from, ctxt);
        let JoinNodesResult {
            index: to_idx,
            performed_merge,
        } = self.join_nodes(to, ctxt);
        if performed_merge {
            from_idx = self.lookup(*from.iter().next().unwrap()).unwrap();
        }
        let _ = self.add_edge_via_indices(from_idx, to_idx, weight, ctxt);
        pcg_validity_assert!(self.is_acyclic(), "Graph contains cycles after adding edge");
    }

    /// Returns the leaf nodes (nodes with no incoming edges)
    pub(crate) fn leaf_nodes(&self) -> Vec<Coupled<N>> {
        self.leaf_node_indices()
            .into_iter()
            .map(|idx| self.inner.node_weight(idx).unwrap().nodes.clone())
            .collect()
    }

    pub(crate) fn leaf_node_indices(&self) -> Vec<NodeIndex> {
        self.inner
            .node_indices()
            .filter(|idx| self.inner.neighbors(*idx).count() == 0)
            .collect()
    }

    pub(crate) fn mut_leaf_nodes(&mut self, f: impl Fn(&mut NodeData<N, E>)) {
        self.leaf_node_indices()
            .into_iter()
            .for_each(|idx| f(self.inner.node_weight_mut(idx).unwrap()));
    }

    pub(crate) fn parents(&self, node: &Coupled<N>) -> Vec<(Coupled<N>, FxHashSet<E>)> {
        let node_idx = self.lookup(*node.iter().next().unwrap()).unwrap();
        self.inner
            .edges_directed(node_idx, Direction::Incoming)
            .map(|e| {
                let source = self.inner.node_weight(e.source()).unwrap().nodes.clone();
                (source, e.weight().clone())
            })
            .collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct HyperEdge<N> {
    lhs: BTreeSet<N>,
    rhs: BTreeSet<N>,
}

impl<N: Ord> HyperEdge<N> {
    pub fn lhs(&self) -> &BTreeSet<N> {
        &self.lhs
    }
    pub fn rhs(&self) -> &BTreeSet<N> {
        &self.rhs
    }
}

impl<N, E> fmt::Display for DisjointSetGraph<N, E>
where
    N: Eq + Hash + Clone + fmt::Display + Copy + Ord + fmt::Debug,
    E: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for edge in self.inner.edge_references() {
            let source = self.inner.node_weight(edge.source()).unwrap();
            let target = self.inner.node_weight(edge.target()).unwrap();
            writeln!(f, "{source:?} -> {target:?}")?;
        }
        Ok(())
    }
}
