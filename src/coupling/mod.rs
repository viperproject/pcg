use petgraph::algo::kosaraju_scc;
use petgraph::dot::{Config, Dot};
use petgraph::graph::{EdgeIndex, Frozen, NodeIndex};
use petgraph::visit::EdgeRef;
use petgraph::{Direction, Graph};
use smallvec::SmallVec;
use std::collections::BTreeSet;
use std::fmt;
use std::hash::Hash;

use crate::coupling::coupled::Coupled;
use crate::pcg_validity_assert;
use crate::rustc_interface::data_structures::fx::FxHashSet;
use crate::utils::display::DisplayWithCompilerCtxt;
use crate::utils::CompilerCtxt;
use crate::visualization::dot_graph::DotGraph;

pub mod coupled;

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

impl<'tcx, N: Copy + Ord + Clone + Hash + std::fmt::Debug, E: Clone + Eq + Hash>
    DisjointSetGraph<N, E>
{
    pub(crate) fn inner(&self) -> &petgraph::Graph<NodeData<N, E>, FxHashSet<E>> {
        &self.inner
    }

    pub(crate) fn new() -> Self {
        DisjointSetGraph {
            inner: petgraph::Graph::new(),
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

    fn to_dot(&self, repacker: CompilerCtxt<'_, 'tcx>) -> String
    where
        N: DisplayWithCompilerCtxt<'tcx>,
    {
        let arena = bumpalo::Bump::new();
        let to_render: petgraph::Graph<&str, ()> = self.inner.clone().map(
            |_, e| {
                let node_name = format!(
                    "{}\n",
                    e.nodes.iter().fold(String::from("{"), |mut acc, x| {
                        acc.push_str(&x.to_short_string(repacker));
                        acc.push_str(", ");
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

    pub(crate) fn render_with_imgcat(&self, repacker: CompilerCtxt<'_, 'tcx>, msg: &str)
    where
        N: DisplayWithCompilerCtxt<'tcx>,
    {
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

    pub(crate) fn insert_endpoint(&mut self, endpoint: Coupled<N>) -> petgraph::prelude::NodeIndex {
        let JoinNodesResult { index, .. } = self.join_nodes(&endpoint);
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
    pub(crate) fn join_nodes(&mut self, nodes: &Coupled<N>) -> JoinNodesResult
    where
        N: std::fmt::Debug,
    {
        match self.get_node_indices(nodes) {
            GetNodeIndicesResult::AlreadyJoined(node_index) => {
                JoinNodesResult {
                    index: node_index,
                    performed_merge: false,
                }
            }
            GetNodeIndicesResult::NoneExist => {
                let idx = self.inner.add_node(NodeData {
                    nodes: nodes.clone(),
                    inner_edges: FxHashSet::default(),
                });
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
                self.merge_sccs();
                let (new_index, _) = self.lookup_in_graph(*nodes.iter().next().unwrap()).unwrap();
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
        self.lookup_in_graph(node).map(|(idx, _)| idx)
    }

    pub(crate) fn is_acyclic(&self) -> bool {
        !petgraph::algo::is_cyclic_directed(&self.inner)
    }

    pub(crate) fn join(&mut self, other: &Self) {
        for (source, target, weight) in other.edges() {
            let JoinNodesResult {
                index: mut source_idx,
                ..
            } = self.join_nodes(&source);
            let JoinNodesResult {
                index: target_idx,
                performed_merge,
            } = self.join_nodes(&target);
            if performed_merge {
                source_idx = self.lookup(*source.iter().next().unwrap()).unwrap();
            }
            let _ = self.add_edge_via_indices(source_idx, target_idx, weight);
        }
    }

    /// Merges all cycles into single nodes. **IMPORTANT**: After performing this
    /// operation, the indices of the nodes may change.
    pub(crate) fn merge_sccs(&mut self) {
        if self.is_acyclic() {
            tracing::info!("Graph is already acyclic");
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
                self.merge_sccs();
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

    pub(crate) fn add_edge(&mut self, from: &Coupled<N>, to: &Coupled<N>, weight: FxHashSet<E>) {
        pcg_validity_assert!(
            self.is_acyclic(),
            "Graph contains cycles before adding edge"
        );
        pcg_validity_assert!(from.is_disjoint(to), "Non-disjoint edges");
        let JoinNodesResult {
            index: mut from_idx,
            ..
        } = self.join_nodes(from);
        let JoinNodesResult {
            index: to_idx,
            performed_merge,
        } = self.join_nodes(to);
        if performed_merge {
            from_idx = self.lookup(*from.iter().next().unwrap()).unwrap();
        }
        let _ = self.add_edge_via_indices(from_idx, to_idx, weight);
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rustc_interface::data_structures::fx::FxHashSet;
    use std::collections::BTreeSet;

    // Simple mock types for testing
    #[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
    struct TestNode<T>(T);

    #[derive(Clone, Debug, PartialEq, Eq, Hash)]
    struct TestEdge(String);

    type TestGraph<T = i32> = DisjointSetGraph<TestNode<T>, TestEdge>;
    type TestCoupled<T> = Coupled<TestNode<T>>;

    fn create_coupled<T: Copy + Ord + Hash + Eq + fmt::Debug>(nodes: &[T]) -> TestCoupled<T> {
        let mut coupled = TestCoupled::empty();
        for &node in nodes {
            coupled.insert(TestNode(node));
        }
        coupled
    }

    #[test]
    fn test_empty_graph() {
        let graph: TestGraph = DisjointSetGraph::new();
        assert!(graph.is_acyclic());
        assert_eq!(graph.leaf_nodes().len(), 0);
    }

    #[test]
    fn test_insert_single_node() {
        let mut graph: TestGraph = DisjointSetGraph::new();

        let coupled = create_coupled(&[1]);
        let idx = graph.insert_endpoint(coupled.clone());

        assert!(graph.is_acyclic());
        assert_eq!(graph.lookup(TestNode(1)), Some(idx));
        assert_eq!(graph.leaf_nodes().len(), 1);
        assert_eq!(graph.leaf_nodes()[0], coupled);
    }

    #[test]
    fn test_insert_multiple_nodes() {
        let mut graph: TestGraph = DisjointSetGraph::new();

        let coupled1 = create_coupled(&[1]);
        let coupled2 = create_coupled(&[2]);
        let coupled3 = create_coupled(&[3]);

        let idx1 = graph.insert_endpoint(coupled1.clone());
        let idx2 = graph.insert_endpoint(coupled2.clone());
        let idx3 = graph.insert_endpoint(coupled3.clone());

        assert!(graph.is_acyclic());
        assert_eq!(graph.lookup(TestNode(1)), Some(idx1));
        assert_eq!(graph.lookup(TestNode(2)), Some(idx2));
        assert_eq!(graph.lookup(TestNode(3)), Some(idx3));
        assert_eq!(graph.leaf_nodes().len(), 3);
    }

    #[test]
    fn test_join_nodes_same_coupled() {
        let mut graph: TestGraph = DisjointSetGraph::new();

        let coupled = create_coupled(&[1, 2]);
        let result = graph.join_nodes(&coupled);

        assert!(!result.performed_merge);
        assert_eq!(graph.lookup(TestNode(1)), Some(result.index));
        assert_eq!(graph.lookup(TestNode(2)), Some(result.index));

        // Joining the same nodes again should return the same index
        let result2 = graph.join_nodes(&coupled);
        assert!(!result2.performed_merge);
        assert_eq!(result.index, result2.index);
    }

    #[test]
    fn test_join_nodes_different_coupled() {
        let mut graph: TestGraph = DisjointSetGraph::new();

        let coupled1 = create_coupled(&[1]);
        let coupled2 = create_coupled(&[2]);
        let coupled_merged = create_coupled(&[1, 2]);

        let idx1 = graph.insert_endpoint(coupled1);
        let idx2 = graph.insert_endpoint(coupled2);

        // Initially different indices
        assert_ne!(idx1, idx2);

        // Join them
        let result = graph.join_nodes(&coupled_merged);
        assert!(result.performed_merge);

        // Both nodes should now point to the same index
        let lookup1 = graph.lookup(TestNode(1)).unwrap();
        let lookup2 = graph.lookup(TestNode(2)).unwrap();
        assert_eq!(lookup1, lookup2);
    }

    #[test]
    fn test_add_edge_simple() {
        let mut graph: TestGraph = DisjointSetGraph::new();

        let from = create_coupled(&[1]);
        let to = create_coupled(&[2]);
        let edge_weight = FxHashSet::from_iter([TestEdge("edge1".to_string())]);

        graph.add_edge(&from, &to, edge_weight.clone());

        assert!(graph.is_acyclic());
        assert_eq!(graph.leaf_nodes().len(), 1);
        assert_eq!(graph.leaf_nodes()[0], to);

        let edges: Vec<_> = graph.edges().collect();
        assert_eq!(edges.len(), 1);
        assert_eq!(edges[0].0, from);
        assert_eq!(edges[0].1, to);
        assert_eq!(edges[0].2, edge_weight);
    }

    #[test]
    fn test_add_multiple_edges_acyclic() {
        let mut graph: TestGraph = DisjointSetGraph::new();

        let node1 = create_coupled(&[1]);
        let node2 = create_coupled(&[2]);
        let node3 = create_coupled(&[3]);
        let edge_weight = FxHashSet::from_iter([TestEdge("edge".to_string())]);

        // Create a chain: 1 -> 2 -> 3
        graph.add_edge(&node1, &node2, edge_weight.clone());
        graph.add_edge(&node2, &node3, edge_weight.clone());

        assert!(graph.is_acyclic());
        assert_eq!(graph.leaf_nodes().len(), 1);
        assert_eq!(graph.leaf_nodes()[0], node3);

        let edges: Vec<_> = graph.edges().collect();
        assert_eq!(edges.len(), 2);
    }

    #[test]
    fn test_simple_cycle_creates_scc() {
        let mut graph: TestGraph = DisjointSetGraph::new();

        let node1 = create_coupled(&[1]);
        let node2 = create_coupled(&[2]);
        let edge_weight = FxHashSet::from_iter([TestEdge("edge".to_string())]);

        // Create a cycle: 1 -> 2 -> 1
        graph.add_edge(&node1, &node2, edge_weight.clone());
        graph.add_edge(&node2, &node1, edge_weight.clone());

        assert!(graph.is_acyclic());

        // Both nodes should now be in the same SCC
        let idx1 = graph.lookup(TestNode(1)).unwrap();
        let idx2 = graph.lookup(TestNode(2)).unwrap();
        assert_eq!(idx1, idx2);

        // There should be only one node in the graph now
        assert_eq!(graph.inner().node_count(), 1);
        assert_eq!(graph.leaf_nodes().len(), 1);

        // The merged node should contain both original nodes
        let merged_node = &graph.leaf_nodes()[0];
        assert!(merged_node.contains(&TestNode(1)));
        assert!(merged_node.contains(&TestNode(2)));
    }

    #[test]
    fn test_three_node_cycle() {
        let mut graph: TestGraph = DisjointSetGraph::new();

        let node1 = create_coupled(&[1]);
        let node2 = create_coupled(&[2]);
        let node3 = create_coupled(&[3]);
        let edge_weight = FxHashSet::from_iter([TestEdge("edge".to_string())]);

        // Create a cycle: 1 -> 2 -> 3 -> 1
        graph.add_edge(&node1, &node2, edge_weight.clone());
        graph.add_edge(&node2, &node3, edge_weight.clone());
        graph.add_edge(&node3, &node1, edge_weight.clone());

        assert!(graph.is_acyclic());

        // All nodes should now be in the same SCC
        let idx1 = graph.lookup(TestNode(1)).unwrap();
        let idx2 = graph.lookup(TestNode(2)).unwrap();
        let idx3 = graph.lookup(TestNode(3)).unwrap();
        assert_eq!(idx1, idx2);
        assert_eq!(idx2, idx3);

        // There should be only one node in the graph now
        assert_eq!(graph.inner().node_count(), 1);
        assert_eq!(graph.leaf_nodes().len(), 1);

        // The merged node should contain all original nodes
        let merged_node = &graph.leaf_nodes()[0];
        assert!(merged_node.contains(&TestNode(1)));
        assert!(merged_node.contains(&TestNode(2)));
        assert!(merged_node.contains(&TestNode(3)));
    }

    #[test]
    fn test_complex_graph_with_multiple_sccs() {
        let mut graph: TestGraph = DisjointSetGraph::new();

        let edge_weight = FxHashSet::from_iter([TestEdge("edge".to_string())]);

        // Create a more complex graph:
        // SCC1: 1 <-> 2
        // SCC2: 3 <-> 4
        // SCC1 -> SCC2 -> 5

        // First SCC: 1 <-> 2
        graph.add_edge(
            &create_coupled(&[1]),
            &create_coupled(&[2]),
            edge_weight.clone(),
        );
        graph.add_edge(
            &create_coupled(&[2]),
            &create_coupled(&[1]),
            edge_weight.clone(),
        );

        // Second SCC: 3 <-> 4
        graph.add_edge(
            &create_coupled(&[3]),
            &create_coupled(&[4]),
            edge_weight.clone(),
        );
        graph.add_edge(
            &create_coupled(&[4]),
            &create_coupled(&[3]),
            edge_weight.clone(),
        );

        // Connect SCCs and add leaf
        graph.add_edge(
            &create_coupled(&[1]),
            &create_coupled(&[3]),
            edge_weight.clone(),
        );
        graph.add_edge(
            &create_coupled(&[3]),
            &create_coupled(&[5]),
            edge_weight.clone(),
        );

        assert!(graph.is_acyclic());

        // Check SCCs were formed correctly
        let idx1 = graph.lookup(TestNode(1)).unwrap();
        let idx2 = graph.lookup(TestNode(2)).unwrap();
        let idx3 = graph.lookup(TestNode(3)).unwrap();
        let idx4 = graph.lookup(TestNode(4)).unwrap();
        let idx5 = graph.lookup(TestNode(5)).unwrap();

        assert_eq!(idx1, idx2); // 1 and 2 in same SCC
        assert_eq!(idx3, idx4); // 3 and 4 in same SCC
        assert_ne!(idx1, idx3); // Different SCCs
        assert_ne!(idx3, idx5); // 5 is separate

        // There should be 3 nodes in the graph now (2 SCCs + 1 individual node)
        assert_eq!(graph.inner().node_count(), 3);

        // Leaf should be node 5
        assert_eq!(graph.leaf_nodes().len(), 1);
        assert_eq!(graph.leaf_nodes()[0], create_coupled(&[5]));
    }

    #[test]
    fn test_parents_function() {
        let mut graph: TestGraph = DisjointSetGraph::new();

        let node1 = create_coupled(&[1]);
        let node2 = create_coupled(&[2]);
        let node3 = create_coupled(&[3]);
        let edge_weight1 = FxHashSet::from_iter([TestEdge("edge1".to_string())]);
        let edge_weight2 = FxHashSet::from_iter([TestEdge("edge2".to_string())]);

        // Create: 1 -> 3, 2 -> 3
        graph.add_edge(&node1, &node3, edge_weight1.clone());
        graph.add_edge(&node2, &node3, edge_weight2.clone());

        let parents = graph.parents(&node3);
        assert_eq!(parents.len(), 2);

        let parent_nodes: BTreeSet<_> = parents.iter().map(|(n, _)| n.clone()).collect();
        assert!(parent_nodes.contains(&node1));
        assert!(parent_nodes.contains(&node2));
    }

    #[test]
    fn test_is_root() {
        let mut graph: TestGraph = DisjointSetGraph::new();

        let node1 = create_coupled(&[1]);
        let node2 = create_coupled(&[2]);
        let edge_weight = FxHashSet::from_iter([TestEdge("edge".to_string())]);

        // Create: 1 -> 2
        graph.add_edge(&node1, &node2, edge_weight);

        assert!(graph.is_root(&node1)); // 1 has no incoming edges
        assert!(!graph.is_root(&node2)); // 2 has incoming edge from 1
    }

    #[test]
    fn test_merge_sccs_with_existing_cycle() {
        let mut graph: TestGraph = DisjointSetGraph::new();

        let edge_weight = FxHashSet::from_iter([TestEdge("edge".to_string())]);

        // Manually create a cycle without using add_edge
        let idx1 = graph.insert_endpoint(create_coupled(&[1]));
        let idx2 = graph.insert_endpoint(create_coupled(&[2]));

        // Manually add edges to create a cycle
        graph.inner.add_edge(idx1, idx2, edge_weight.clone());
        graph.inner.add_edge(idx2, idx1, edge_weight.clone());

        // Verify we have a cycle
        assert!(!graph.is_acyclic());

        // Now merge SCCs
        graph.merge_sccs();

        // Should be acyclic now
        assert!(graph.is_acyclic());

        // Both nodes should be in the same SCC
        let lookup1 = graph.lookup(TestNode(1)).unwrap();
        let lookup2 = graph.lookup(TestNode(2)).unwrap();
        assert_eq!(lookup1, lookup2);
    }

    #[test]
    fn test_add_edge_via_indices() {
        let mut graph: TestGraph = DisjointSetGraph::new();

        let idx1 = graph.insert_endpoint(create_coupled(&[1]));
        let idx2 = graph.insert_endpoint(create_coupled(&[2]));
        let edge_weight = FxHashSet::from_iter([TestEdge("direct_edge".to_string())]);

        let result = graph.add_edge_via_indices(idx1, idx2, edge_weight.clone());

        match result {
            AddEdgeResult::DidNotMergeNodes => {
                assert!(graph.is_acyclic());
                let edges: Vec<_> = graph.edges().collect();
                assert_eq!(edges.len(), 1);
            }
            AddEdgeResult::MergedNodes => {
                panic!("Should not have merged nodes in this simple case");
            }
        }
    }

    #[test]
    fn test_add_edge_via_indices_creates_merge() {
        let mut graph: TestGraph = DisjointSetGraph::new();

        let idx1 = graph.insert_endpoint(create_coupled(&[1]));
        let idx2 = graph.insert_endpoint(create_coupled(&[2]));
        let edge_weight = FxHashSet::from_iter([TestEdge("edge".to_string())]);

        // Create cycle: 1 -> 2 -> 1
        let _ = graph.add_edge_via_indices(idx1, idx2, edge_weight.clone());
        let result = graph.add_edge_via_indices(idx2, idx1, edge_weight.clone());

        match result {
            AddEdgeResult::MergedNodes => {
                assert!(graph.is_acyclic());
                // Nodes should be merged
                let lookup1 = graph.lookup(TestNode(1)).unwrap();
                let lookup2 = graph.lookup(TestNode(2)).unwrap();
                assert_eq!(lookup1, lookup2);
            }
            AddEdgeResult::DidNotMergeNodes => {
                panic!("Should have merged nodes due to cycle");
            }
        }
    }

    #[test]
    fn test_edge_weights_preserved_after_scc_merge() {
        let mut graph: TestGraph = DisjointSetGraph::new();

        let node1 = create_coupled(&[1]);
        let node2 = create_coupled(&[2]);
        let node3 = create_coupled(&[3]);

        let edge_weight1 = FxHashSet::from_iter([TestEdge("edge1".to_string())]);
        let edge_weight2 = FxHashSet::from_iter([TestEdge("edge2".to_string())]);
        let edge_weight3 = FxHashSet::from_iter([TestEdge("edge3".to_string())]);

        // Create cycle with different edge weights: 1 -> 2 -> 1
        graph.add_edge(&node1, &node2, edge_weight1);
        graph.add_edge(&node2, &node1, edge_weight2);

        // Add edge from merged node to external node
        graph.add_edge(&node1, &node3, edge_weight3.clone());

        assert!(graph.is_acyclic());

        // Check that the edge to node3 still exists with correct weight
        let edges: Vec<_> = graph.edges().collect();
        let edge_to_3 = edges
            .iter()
            .find(|(_, target, _)| target.contains(&TestNode(3)))
            .unwrap();
        assert_eq!(edge_to_3.2, edge_weight3);
    }

    #[test]
    fn test_join() {
        let mut graph1: TestGraph = DisjointSetGraph::new();
        let mut graph2: TestGraph = DisjointSetGraph::new();

        let node1 = create_coupled(&[1]);
        let node2 = create_coupled(&[2, 3]);
        let node3 = create_coupled(&[3]);

        graph1.add_edge(&node1, &node2, Default::default());
        graph2.add_edge(&node1, &node3, Default::default());

        graph1.join(&graph2);

        assert!(graph1.is_acyclic());
        assert_eq!(graph1.inner().node_count(), 2);
        assert_eq!(graph1.leaf_nodes().len(), 1);
        // assert_eq!(graph1.leaf_nodes()[0], create_coupled(&[1, 2, 3]));
    }

    #[test]
    fn test_join_2() {
        let mut graph1: TestGraph<&str> = DisjointSetGraph::new();
        let mut graph2: TestGraph<&str> = DisjointSetGraph::new();

        let node1 = create_coupled(&["remote1"]);
        let node2 = create_coupled(&["remote128"]);
        let node3 = create_coupled(&["xstart"]);
        let node4 = create_coupled(&["iter32"]);
        let node5 = create_coupled(&["extra0", "iter32", "extra1"]);

        for (from, to) in [
            (node1.clone(), node2.clone()),
            (node1.clone(), node3.clone()),
        ] {
            graph1.add_edge(&from, &to, Default::default());
            graph2.add_edge(&from, &to, Default::default());
        }

        graph1.add_edge(&node3, &node4, Default::default());
        graph2.add_edge(&node3, &node5, Default::default());

        graph1.join(&graph2);

        assert_eq!(graph1.edges().count(), 3);
    }
}
