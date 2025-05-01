use petgraph::dot::{Config, Dot};
use petgraph::graph::NodeIndex;
use petgraph::visit::EdgeRef;
use petgraph::Direction;
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

/// A DAG where each node is a set of elements of type `N`. Cycles are resolved
/// by merging the nodes in the cycle into a single node. The graph is always in
/// a transitively reduced form (see
/// https://en.wikipedia.org/wiki/Transitive_reduction)
#[derive(Clone)]
pub(crate) struct DisjointSetGraph<N, E> {
    pub(crate) inner: petgraph::Graph<Coupled<N>, FxHashSet<E>>,
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
            .map(|idx| self.inner.node_weight(idx).unwrap().clone())
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
            (source.clone(), target.clone(), e.weight().clone())
        })
    }

    fn to_dot(&self, repacker: CompilerCtxt<'_, 'tcx>) -> String {
        let arena = bumpalo::Bump::new();
        let to_render: petgraph::Graph<&str, ()> = self.inner.clone().map(
            |_, e| {
                let node_name = format!(
                    "{}\n",
                    e.iter().fold(String::from("{"), |mut acc, x| {
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

    fn insert(&mut self, node: N) -> petgraph::prelude::NodeIndex {
        if let Some(idx) = self.lookup(node) {
            return idx;
        }
        let idx = self.inner.add_node(BTreeSet::from([node]).into());
        pcg_validity_assert!(
            self.is_acyclic(),
            "Graph contains cycles after inserting node"
        );
        idx
    }

    pub(crate) fn insert_endpoint(
        &mut self,
        endpoint: Coupled<N>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> petgraph::prelude::NodeIndex {
        let JoinNodesResult {
            index,
            performed_merge,
        } = self.join_nodes(&endpoint);
        if performed_merge {
            self.merge_sccs(repacker);
        }
        pcg_validity_assert!(
            self.is_acyclic(),
            "Graph contains cycles after inserting endpoint"
        );
        index
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
            .map(|e| (e.source(), new_idx, e.weight().clone()))
            .chain(
                edges_from_old
                    .filter(|e| e.target() != new_idx)
                    .map(|e| (new_idx, e.target(), e.weight().clone())),
            );
        for (source, target, weight) in to_add.collect::<Vec<_>>() {
            self.inner.update_edge(source, target, weight);
        }
        assert!(self.inner.remove_node(old_idx).is_some());
    }

    /// Joins the nodes in `nodes` into a single coupled node.
    ///
    /// **IMPORTANT**: This will invalidate existing node indices
    #[must_use]
    pub(crate) fn join_nodes(&mut self, nodes: &Coupled<N>) -> JoinNodesResult {
        let mut iter = nodes.iter().cloned();
        let first_elem = iter.next().unwrap();
        let mut idx = self.insert(first_elem);
        let mut changed = false;
        for node in iter {
            let idx2 = self.insert(node);
            if idx2 != idx {
                self.merge_idxs(idx, idx2);
                // Indexes are invalidated after merging
                idx = self.lookup(first_elem).unwrap();
                changed = true;
            }
        }
        // We don't use `idx` here because node indices may change after merging SCCs.
        JoinNodesResult {
            index: self.lookup(*nodes.iter().next().unwrap()).unwrap(),
            performed_merge: changed,
        }
    }

    pub(crate) fn lookup(&self, node: N) -> Option<petgraph::prelude::NodeIndex> {
        self.inner.node_indices().find(|idx| {
            self.inner
                .node_weight(*idx)
                .is_some_and(|w| w.contains(&node))
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
        let old_graph = self.clone(); // For debugging

        'outer: loop {
            let sccs = petgraph::algo::kosaraju_scc(&self.inner);
            for scc in sccs {
                if scc.len() > 1 {
                    self.merge_idxs(scc[0], scc[1]);
                    // We need to recompute sccs because node indices may have changed
                    continue 'outer;
                } else if let Some(edge_idx) = self.inner.find_edge(scc[0], scc[0]) {
                    self.inner.remove_edge(edge_idx);
                }
            }
            break;
        }

        if validity_checks_enabled() && !self.is_acyclic() && coupling_imgcat_debug() {
            old_graph.render_with_imgcat(repacker, "Before merging SCCs");
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
        }
        AddEdgeResult::DidNotMergeNodes
    }

    pub(crate) fn add_edge(
        &mut self,
        from: &Coupled<N>,
        to: &Coupled<N>,
        weight: FxHashSet<E>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) {
        pcg_validity_assert!(
            self.is_acyclic(),
            "Graph contains cycles before adding edge"
        );
        pcg_validity_assert!(
            from != to,
            "Self-loop edge {}",
            from.iter()
                .map(|x| x.to_short_string(repacker))
                .collect::<Vec<_>>()
                .join(", ")
        );
        let mut should_merge_sccs;
        if from.is_empty() {
            assert!(!to.is_empty());
            should_merge_sccs = self.join_nodes(to).performed_merge;
        } else if to.is_empty() {
            assert!(!from.is_empty());
            should_merge_sccs = self.join_nodes(from).performed_merge;
        } else {
            let mut from_idx = self.join_nodes(from);
            should_merge_sccs = from_idx.performed_merge;
            let mut to_idx = self.join_nodes(to);
            should_merge_sccs |= to_idx.performed_merge;
            if should_merge_sccs {
                self.merge_sccs(repacker);
                from_idx.index = self.lookup(*from.iter().next().unwrap()).unwrap();
                to_idx.index = self.lookup(*to.iter().next().unwrap()).unwrap();
                should_merge_sccs = false;
            }
            let _ = self.add_edge_via_indices(from_idx.index, to_idx.index, weight, repacker);
        }
        if should_merge_sccs {
            self.merge_sccs(repacker);
        }
        pcg_validity_assert!(self.is_acyclic(), "Graph contains cycles after adding edge");
    }

    /// Returns the leaf nodes (nodes with no incoming edges)
    pub(crate) fn leaf_nodes(&self) -> Vec<Coupled<N>> {
        self.inner
            .node_indices()
            .filter(|idx| self.inner.neighbors(*idx).count() == 0)
            .map(|idx| self.inner.node_weight(idx).unwrap().clone())
            .collect()
    }

    pub(crate) fn parents(&self, node: &Coupled<N>) -> Vec<(Coupled<N>, FxHashSet<E>)> {
        let node_idx = self.lookup(*node.iter().next().unwrap()).unwrap();
        self.inner
            .edges_directed(node_idx, Direction::Incoming)
            .map(|e| {
                let source = self.inner.node_weight(e.source()).unwrap().clone();
                (source, e.weight().clone())
            })
            .collect()
    }

    #[allow(dead_code)]
    pub(crate) fn children(&self, node: &Coupled<N>) -> Vec<(Coupled<N>, FxHashSet<E>)> {
        let node_idx = self.lookup(*node.iter().next().unwrap()).unwrap();
        self.inner
            .edges_directed(node_idx, Direction::Outgoing)
            .map(|e| {
                let source = self.inner.node_weight(e.source()).unwrap().clone();
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
