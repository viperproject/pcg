use petgraph::dot::{Config, Dot};
use petgraph::visit::EdgeRef;
use petgraph::Direction;
use std::collections::{BTreeSet, HashSet};
use std::fmt;
use std::hash::Hash;

/// A DAG where each node is a set of elements of type `N`. Cycles are resolved
/// by merging the nodes in the cycle into a single node. The graph is always in
/// a transitively reduced form (see
/// https://en.wikipedia.org/wiki/Transitive_reduction)
pub struct DisjointSetGraph<N> {
    inner: petgraph::Graph<BTreeSet<N>, ()>,
}

pub type Endpoint<N> = BTreeSet<N>;

impl<N: Copy + Ord + Clone + fmt::Display> DisjointSetGraph<N> {
    pub fn new() -> Self {
        DisjointSetGraph {
            inner: petgraph::Graph::new(),
        }
    }

    pub fn nodes(&self) -> BTreeSet<N> {
        self.edges()
            .map(|(from, to)| from.union(&to).cloned().collect::<BTreeSet<_>>())
            .flatten()
            .collect()
    }

    pub fn isolated_endpoints(&self) -> BTreeSet<Endpoint<N>> {
        self.inner
            .node_indices()
            .filter(|idx| self.inner.neighbors_undirected(*idx).count() == 0)
            .map(|idx| self.inner.node_weight(idx).unwrap().clone())
            .collect()
    }

    pub fn endpoints(&self) -> BTreeSet<BTreeSet<N>> {
        self.edges()
            .flat_map(|(from, to)| [from, to].into_iter())
            .collect::<BTreeSet<_>>()
    }

    pub fn edges(&self) -> impl Iterator<Item = (BTreeSet<N>, BTreeSet<N>)> + '_ {
        self.inner.edge_references().map(|e| {
            let source = self.inner.node_weight(e.source()).unwrap();
            let target = self.inner.node_weight(e.target()).unwrap();
            (
                source.iter().cloned().collect(),
                target.iter().cloned().collect(),
            )
        })
    }

    fn to_dot(&self) -> String {
        let arena = bumpalo::Bump::new();
        let to_render: petgraph::Graph<&str, ()> = self.inner.clone().map(
            |_, e| {
                let node_name = format!(
                    "{}\n",
                    e.iter().fold(String::from("{"), |mut acc, x| {
                        acc.push_str(&format!("{}\n", x));
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

    pub fn render_with_imgcat(&self) {
        fn go<N: Copy + Ord + Clone + fmt::Display>(
            graph: &DisjointSetGraph<N>,
        ) -> Result<(), std::io::Error> {
            let dot = graph.to_dot();
            DotGraph::render_with_imgcat(&dot, "")
        }

        // This function is just for debugging, so we don't care if it fails
        go(self).unwrap_or_else(|e| {
            eprintln!("Error rendering graph: {}", e);
        });
    }

    pub fn node_count(&self) -> usize {
        self.inner.node_count()
    }

    pub fn edge_count(&self) -> usize {
        self.inner.edge_count()
    }

    pub fn insert(&mut self, node: N) -> petgraph::prelude::NodeIndex {
        if let Some(idx) = self.lookup(node) {
            return idx;
        }
        self.inner.add_node(BTreeSet::from([node]))
    }

    pub fn insert_endpoint(&mut self, endpoint: BTreeSet<N>) -> petgraph::prelude::NodeIndex {
        self.join_nodes(&endpoint)
    }

    pub fn merge_into_idx(
        &mut self,
        new_idx: petgraph::prelude::NodeIndex,
        old_idx: petgraph::prelude::NodeIndex,
    ) {
        let old_node_data = self.inner.node_weight(old_idx).unwrap().clone();
        let new_idx_weight = self.inner.node_weight_mut(new_idx).unwrap();
        new_idx_weight.extend(old_node_data.into_iter());
        let to_add = self
            .inner
            .edges_directed(old_idx, Direction::Incoming)
            .filter(|e| e.source() != new_idx)
            .map(|e| (e.source(), new_idx))
            .chain(
                self.inner
                    .edges_directed(old_idx, Direction::Outgoing)
                    .filter(|e| e.target() != new_idx)
                    .map(|e| (new_idx, e.target())),
            );
        for (source, target) in to_add.collect::<Vec<_>>() {
            self.inner.update_edge(source, target, ());
        }
        self.inner.remove_node(old_idx);
    }

    fn join_nodes(&mut self, nodes: &BTreeSet<N>) -> petgraph::prelude::NodeIndex {
        let mut iter = nodes.iter().cloned();
        let idx = self.insert(iter.next().unwrap());
        while let Some(node) = iter.next() {
            let idx2 = self.insert(node);
            if idx2 != idx {
                self.merge_into_idx(idx, idx2);
            }
        }
        idx
    }

    pub fn lookup(&self, node: N) -> Option<petgraph::prelude::NodeIndex> {
        self.inner.node_indices().find(|idx| {
            self.inner
                .node_weight(*idx)
                .map_or(false, |w| w.contains(&node))
        })
    }

    pub fn merge(&mut self, other: &Self) {
        for (source, target) in other.edges() {
            let source_idx = self.join_nodes(&source);
            let target_idx = self.join_nodes(&target);
            if source_idx != target_idx {
                self.inner.update_edge(source_idx, target_idx, ());
            }
        }
        // Compute strongly connected components after merging
        let sccs = petgraph::algo::kosaraju_scc(&self.inner);
        for scc in sccs {
            if scc.len() > 1 {
                // Merge all nodes in the SCC into the first node
                let first = scc[0];
                for other in &scc[1..] {
                    self.merge_into_idx(first, *other);
                }
            }
        }

        debug_assert!(
            petgraph::algo::is_cyclic_directed(&self.inner) == false,
            "Graph contains cycles after SCC computation"
        );

        debug_assert_eq!(
            petgraph::algo::connected_components(&self.inner),
            1,
            "Graph has multiple connected components"
        );

        let toposort = petgraph::algo::toposort(&self.inner, None).unwrap();
        let (g, revmap) =
            petgraph::algo::tred::dag_to_toposorted_adjacency_list(&self.inner, &toposort);

        let (tred, _) = petgraph::algo::tred::dag_transitive_reduction_closure::<_, u32>(&g);
        self.inner.retain_edges(|slf, ei| {
            let endpoints = slf.edge_endpoints(ei).unwrap();
            tred.contains_edge(revmap[endpoints.0.index()], revmap[endpoints.1.index()])
        });

        debug_assert_eq!(
            petgraph::algo::connected_components(&self.inner),
            1,
            "Graph has multiple connected components"
        );
    }

    pub fn add_edge(&mut self, from: &BTreeSet<N>, to: &BTreeSet<N>) {
        assert!(
            from != to,
            "Self-loop edge {}",
            from.iter()
                .map(|x| format!("{{{}}}", x))
                .collect::<Vec<_>>()
                .join(", ")
        );
        if from.is_empty() {
            assert!(!to.is_empty());
            self.join_nodes(to);
        } else if to.is_empty() {
            assert!(!from.is_empty());
            self.join_nodes(from);
        } else {
            let from_idx = self.join_nodes(from);
            let to_idx = self.join_nodes(to);
            self.inner.update_edge(from_idx, to_idx, ());
        }
    }

    /// Returns the leaf nodes (nodes with no incoming edges)
    pub fn leaf_nodes(&self) -> Vec<BTreeSet<N>> {
        self.inner
            .node_indices()
            .filter(|idx| self.inner.neighbors(*idx).count() == 0)
            .map(|idx| self.inner.node_weight(idx).unwrap().clone())
            .collect()
    }

    pub fn nodes_pointing_to(&self, node: &BTreeSet<N>) -> Vec<BTreeSet<N>> {
        let node_idx = self.lookup(*node.iter().next().unwrap()).unwrap();
        self.inner
            .node_indices()
            .filter(|idx| self.inner.contains_edge(*idx, node_idx))
            .map(|idx| self.inner.node_weight(idx).unwrap().clone())
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

impl<N> fmt::Display for DisjointSetGraph<N>
where
    N: Eq + Hash + Clone + fmt::Display + Copy + Ord + fmt::Debug,
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

use crate::visualization::dot_graph::DotGraph;
