use itertools::Itertools;
use petgraph::algo::kosaraju_scc;
use petgraph::dot::{Config, Dot};
use petgraph::graph::NodeIndex;
use petgraph::visit::EdgeRef;
use petgraph::{Direction, Graph};
use std::collections::BTreeSet;
use std::fmt;
use std::hash::Hash;

use crate::borrow_pcg::abstraction_graph_constructor::Coupled;
use crate::borrow_pcg::graph::coupling_imgcat_debug;
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
    pub(crate) inner: petgraph::Graph<NodeData<N, E>, FxHashSet<E>>,
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
    pub(crate) fn new() -> Self {
        DisjointSetGraph {
            inner: petgraph::Graph::new(),
        }
    }

    pub(crate) fn roots(&self) -> FxHashSet<Coupled<N>> {
        self.inner
            .node_indices()
            .filter(|idx| {
                self.inner
                    .neighbors_directed(*idx, Direction::Incoming)
                    .count()
                    == 0
            })
            .map(|idx| self.inner.node_weight(idx).unwrap().nodes.clone())
            .collect()
    }

    #[allow(dead_code)]
    pub(crate) fn height(&self) -> usize {
        let mut max_height = 0;
        for node in self.roots() {
            let height = petgraph::algo::dijkstra(
                &self.inner,
                self.lookup(*node.iter().next().unwrap()).unwrap(),
                None,
                |_| 1,
            );
            max_height = max_height.max(*height.values().max().unwrap_or(&0));
        }
        max_height
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
            eprintln!("Error rendering graph: {}", e);
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

    /// Joins the nodes in `nodes` into a single coupled node.
    ///
    /// **IMPORTANT**: This will invalidate existing node indices
    #[must_use]
    pub(crate) fn join_nodes(
        &mut self,
        nodes: &Coupled<N>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> JoinNodesResult {
        let indices = nodes
            .iter()
            .map(|n| (n, self.lookup(*n)))
            .unique()
            .collect::<Vec<_>>();
        let candidate_idx = indices.iter().filter_map(|(_, idx)| *idx).next();
        if let Some(candidate_idx) = candidate_idx {
            let mut should_merge = false;
            for (node, idx_opt) in indices {
                match idx_opt {
                    Some(node_idx) => {
                        if node_idx != candidate_idx {
                            should_merge = true;
                            self.inner
                                .add_edge(node_idx, candidate_idx, FxHashSet::default());
                            self.inner
                                .add_edge(candidate_idx, node_idx, FxHashSet::default());
                        }
                    }
                    None => {
                        self.inner
                            .node_weight_mut(candidate_idx)
                            .unwrap()
                            .nodes
                            .insert(*node);
                    }
                }
            }
            if should_merge {
                self.merge_sccs(ctxt);
            }
            JoinNodesResult {
                index: self.lookup(*nodes.iter().next().unwrap()).unwrap(),
                performed_merge: should_merge,
            }
        } else {
            let idx = self.inner.add_node(NodeData {
                nodes: nodes.clone(),
                inner_edges: FxHashSet::default(),
            });
            JoinNodesResult {
                index: idx,
                performed_merge: false,
            }
        }
    }

    pub(crate) fn lookup(&self, node: N) -> Option<petgraph::prelude::NodeIndex> {
        self.inner.node_indices().find(|idx| {
            self.inner
                .node_weight(*idx)
                .is_some_and(|w| w.nodes.contains(&node))
        })
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

        if validity_checks_enabled() && !self.is_acyclic() && coupling_imgcat_debug() {
            self.render_with_imgcat(repacker, "After merging SCCs");
        }

        pcg_validity_assert!(
            self.is_acyclic(),
            "Resulting graph contains cycles after merging SCCs"
        );
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
            if !self.is_acyclic() {
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
        self.inner
            .node_indices()
            .filter(|idx| self.inner.neighbors(*idx).count() == 0)
            .map(|idx| self.inner.node_weight(idx).unwrap().nodes.clone())
            .collect()
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
            writeln!(f, "{:?} -> {:?}", source, target)?;
        }
        Ok(())
    }
}
