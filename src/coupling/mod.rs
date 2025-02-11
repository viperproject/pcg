use petgraph::dot::{Config, Dot};
use petgraph::visit::EdgeRef;
use petgraph::Direction;
use std::collections::BTreeSet;
use std::fmt;
use std::hash::Hash;

#[cfg(debug_assertions)]
use crate::borrows::borrows_graph::coupling_imgcat_debug;
use crate::borrows::coupling_graph_constructor::Coupled;
use crate::visualization::dot_graph::DotGraph;

/// A DAG where each node is a set of elements of type `N`. Cycles are resolved
/// by merging the nodes in the cycle into a single node. The graph is always in
/// a transitively reduced form (see
/// https://en.wikipedia.org/wiki/Transitive_reduction)
#[derive(Clone)]
pub(crate) struct DisjointSetGraph<N> {
    inner: petgraph::Graph<Coupled<N>, ()>,
}

impl<N: Copy + Ord + Clone + fmt::Display + Hash> DisjointSetGraph<N> {
    pub(crate) fn new() -> Self {
        DisjointSetGraph {
            inner: petgraph::Graph::new(),
        }
    }

    pub(crate) fn endpoints(&self) -> BTreeSet<Coupled<N>> {
        self.inner
            .node_indices()
            .map(|idx| self.inner.node_weight(idx).unwrap().clone())
            .collect()
    }

    pub(crate) fn edges(&self) -> impl Iterator<Item = (Coupled<N>, Coupled<N>)> + '_ {
        self.inner.edge_references().map(|e| {
            let source = self.inner.node_weight(e.source()).unwrap();
            let target = self.inner.node_weight(e.target()).unwrap();
            (source.clone(), target.clone())
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

    pub(crate) fn render_with_imgcat(&self, msg: &str) {
        let dot = self.to_dot();
        DotGraph::render_with_imgcat(&dot, msg).unwrap_or_else(|e| {
            eprintln!("Error rendering graph: {}", e);
        });
    }

    fn insert(&mut self, node: N) -> petgraph::prelude::NodeIndex {
        if let Some(idx) = self.lookup(node) {
            return idx;
        }
        let idx = self.inner.add_node(BTreeSet::from([node]).into());
        debug_assert!(
            self.is_acyclic(),
            "Graph contains cycles after inserting node"
        );
        idx
    }

    pub(crate) fn insert_endpoint(&mut self, endpoint: Coupled<N>) -> petgraph::prelude::NodeIndex {
        let idx = self.join_nodes(&endpoint);
        debug_assert!(
            self.is_acyclic(),
            "Graph contains cycles after inserting endpoint"
        );
        idx
    }

    /// Merges the nodes at `old_idx` and `new_idx`.
    ///
    /// **IMPORTANT**: This will invalidate existing node indices
    pub(crate) fn merge_idxs(
        &mut self,
        new_idx: petgraph::prelude::NodeIndex,
        old_idx: petgraph::prelude::NodeIndex,
    ) {
        let old_node_data = self.inner.node_weight(old_idx).unwrap().clone();
        let new_idx_weight = self.inner.node_weight_mut(new_idx).unwrap_or_else(|| {
            panic!(
                "Cannot merge {:?} and {:?} because node {:?} not found",
                new_idx, old_idx, new_idx
            );
        });
        new_idx_weight.merge(old_node_data);
        let edges_to_old = self.inner.edges_directed(old_idx, Direction::Outgoing);
        let edges_from_old = self.inner.edges_directed(old_idx, Direction::Incoming);
        let to_add = edges_to_old
            .filter(|e| e.source() != new_idx)
            .map(|e| (e.source(), new_idx))
            .chain(
                edges_from_old
                    .filter(|e| e.target() != new_idx)
                    .map(|e| (new_idx, e.target())),
            );
        for (source, target) in to_add.collect::<Vec<_>>() {
            self.inner.update_edge(source, target, ());
        }
        assert!(self.inner.remove_node(old_idx).is_some());
    }

    /// Joins the nodes in `nodes` into a single coupled node.
    ///
    /// **IMPORTANT**: This will invalidate existing node indices
    fn join_nodes(&mut self, nodes: &Coupled<N>) -> petgraph::prelude::NodeIndex {
        let mut iter = nodes.iter().cloned();
        let first_elem = iter.next().unwrap();
        let mut idx = self.insert(first_elem);
        while let Some(node) = iter.next() {
            let idx2 = self.insert(node);
            if idx2 != idx {
                self.merge_idxs(idx, idx2);
                // Indexes are invalidated after merging
                idx = self.lookup(first_elem).unwrap();
            }
        }
        self.merge_sccs();
        debug_assert!(
            self.is_acyclic(),
            "Graph contains cycles after joining nodes"
        );
        // We don't use `idx` here because node indices may change after merging SCCs.
        self.lookup(*nodes.iter().next().unwrap()).unwrap()
    }

    fn lookup(&self, node: N) -> Option<petgraph::prelude::NodeIndex> {
        self.inner.node_indices().find(|idx| {
            self.inner
                .node_weight(*idx)
                .map_or(false, |w| w.contains(&node))
        })
    }

    fn is_acyclic(&self) -> bool {
        !petgraph::algo::is_cyclic_directed(&self.inner)
    }

    /// Merges all cycles into single nodes. **IMPORTANT**: After performing this
    /// operation, the indices of the nodes may change.
    fn merge_sccs(&mut self) {
        #[cfg(debug_assertions)]
        let old_graph = self.clone(); // For debugging

        'outer: loop {
            let sccs = petgraph::algo::kosaraju_scc(&self.inner);
            for scc in sccs {
                if scc.len() > 1 {
                    self.merge_idxs(scc[0], scc[1]);
                    // We need to recompute sccs because node indices may have changed
                    continue 'outer;
                } else {
                    if let Some(edge_idx) = self.inner.find_edge(scc[0], scc[0]) {
                        self.inner.remove_edge(edge_idx);
                    }
                }
            }
            break;
        }

        #[cfg(debug_assertions)]
        if !self.is_acyclic() && coupling_imgcat_debug() {
            old_graph.render_with_imgcat("Before merging SCCs");
            self.render_with_imgcat("After merging SCCs");
        }

        debug_assert!(
            self.is_acyclic(),
            "Resulting graph contains cycles after merging SCCs"
        );
    }

    pub(crate) fn merge(&mut self, other: &Self) {
        for (source, target) in other.edges() {
            let source_idx = self.join_nodes(&source);
            let target_idx = self.join_nodes(&target);
            if source_idx != target_idx {
                self.inner.update_edge(source_idx, target_idx, ());
            }
        }

        self.merge_sccs();

        debug_assert!(
            self.is_acyclic(),
            "Graph contains cycles after SCC computation"
        );

        let toposort = petgraph::algo::toposort(&self.inner, None).unwrap();
        let (g, revmap) =
            petgraph::algo::tred::dag_to_toposorted_adjacency_list(&self.inner, &toposort);

        let (tred, _) = petgraph::algo::tred::dag_transitive_reduction_closure::<_, u32>(&g);
        self.inner.retain_edges(|slf, ei| {
            let endpoints = slf.edge_endpoints(ei).unwrap();
            tred.contains_edge(revmap[endpoints.0.index()], revmap[endpoints.1.index()])
        });

        debug_assert!(self.is_acyclic(), "Resulting graph contains cycles");
    }

    pub(crate) fn add_edge(&mut self, from: &Coupled<N>, to: &Coupled<N>) {
        debug_assert!(
            self.is_acyclic(),
            "Graph contains cycles before adding edge"
        );
        debug_assert!(
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
            debug_assert!(
                self.is_acyclic(),
                "Graph contains cycles after joining to nodes (from nodes empty)"
            );
        } else if to.is_empty() {
            assert!(!from.is_empty());
            self.join_nodes(from);
            debug_assert!(
                self.is_acyclic(),
                "Graph contains cycles after joining from nodes (to nodes empty)"
            );
        } else {
            self.join_nodes(from);
            debug_assert!(
                self.is_acyclic(),
                "Graph contains cycles after joining from nodes"
            );
            let to_idx = self.join_nodes(to);
            debug_assert!(
                self.is_acyclic(),
                "Graph contains cycles after joining to nodes"
            );
            let from_idx = self.lookup(*from.iter().next().unwrap()).unwrap();
            self.inner.update_edge(from_idx, to_idx, ());
        }
        self.merge_sccs();
        debug_assert!(self.is_acyclic(), "Graph contains cycles after adding edge");
    }

    /// Returns the leaf nodes (nodes with no incoming edges)
    pub(crate) fn leaf_nodes(&self) -> Vec<Coupled<N>> {
        self.inner
            .node_indices()
            .filter(|idx| self.inner.neighbors(*idx).count() == 0)
            .map(|idx| self.inner.node_weight(idx).unwrap().clone())
            .collect()
    }

    pub(crate) fn endpoints_pointing_to(&self, node: &Coupled<N>) -> Vec<Coupled<N>> {
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
