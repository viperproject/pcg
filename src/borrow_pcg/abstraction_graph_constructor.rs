use std::collections::BTreeSet;

use petgraph::algo::has_path_connecting;
use smallvec::SmallVec;

use super::{
    edge::kind::BorrowPcgEdgeKind,
    graph::{coupling_imgcat_debug, BorrowsGraph},
    region_projection::PcgRegion,
};
use crate::{
    borrow_checker::BorrowCheckerInterface,
    borrow_pcg::abstraction::node::AbstractionGraphNode,
    coupling::{AddEdgeResult, JoinNodesResult}, validity_checks_enabled,
};
use crate::{
    coupling,
    pcg::PCGNode,
    pcg_validity_assert,
    rustc_interface::data_structures::fx::FxHashSet,
    rustc_interface::middle::mir::{BasicBlock, Location},
    utils::{display::DisplayWithCompilerCtxt, validity::HasValidityCheck, CompilerCtxt},
};

/// A collection of coupled PCG nodes. They will expire at the same time, and only one
/// node in the set will be alive.
///
/// These nodes are introduced for loops: place `a` may borrow from `b` or place
/// `b` may borrow from `a` depending on the number of loop iterations. Therefore,
/// `a` and `b` are coupled and only one can be accessed.
///
/// Internally, the nodes are stored in a `Vec` to allow for mutation
#[derive(Clone, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub struct Coupled<T>(SmallVec<[T; 4]>);

impl<T: Copy + Eq> Coupled<T> {
    pub(crate) fn is_disjoint(&self, other: &Self) -> bool {
        self.0.iter().all(|x| !other.0.contains(x))
    }

    pub(crate) fn empty() -> Self {
        Self(SmallVec::new())
    }

    pub(crate) fn insert(&mut self, item: T) {
        if !self.0.contains(&item) {
            self.0.push(item);
        }
    }

    pub(crate) fn merge(&mut self, other: &Self) {
        for item in other.0.iter() {
            self.insert(*item);
        }
    }

    pub(crate) fn mutate(&mut self, f: impl Fn(&mut T)) {
        for item in self.0.iter_mut() {
            f(item);
        }
    }
}

impl<'tcx, T: HasValidityCheck<'tcx>> HasValidityCheck<'tcx> for Coupled<T> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        for t in self.0.iter() {
            t.check_validity(ctxt)?;
        }
        Ok(())
    }
}

impl<'tcx, T: DisplayWithCompilerCtxt<'tcx>> DisplayWithCompilerCtxt<'tcx> for Coupled<T> {
    fn to_short_string(&self, repacker: CompilerCtxt<'_, 'tcx>) -> String {
        format!(
            "{{{}}}",
            self.0
                .iter()
                .map(|t| t.to_short_string(repacker))
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

pub(crate) type AbstractionGraph<'tcx, 'graph> =
    coupling::DisjointSetGraph<AbstractionGraphNode<'tcx>, &'graph BorrowPcgEdgeKind<'tcx>>;

impl<'tcx> Coupled<AbstractionGraphNode<'tcx>> {
    pub(crate) fn region_repr(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Option<PcgRegion> {
        self.iter().find_map(|n| match n.to_pcg_node() {
            PCGNode::RegionProjection(rp) => Some(rp.region(ctxt)),
            _ => None,
        })
    }

    pub(crate) fn is_remote(&self) -> bool {
        self.iter().any(|n| match n.to_pcg_node() {
            PCGNode::Place(p) => p.is_remote(),
            PCGNode::RegionProjection(rp) => rp.base().is_remote(),
        })
    }
}

impl<'tcx, 'graph> AbstractionGraph<'tcx, 'graph> {
    pub(crate) fn add_edge_with_ctxt(
        &mut self,
        from: &Coupled<AbstractionGraphNode<'tcx>>,
        to: &Coupled<AbstractionGraphNode<'tcx>>,
        weight: FxHashSet<&'graph BorrowPcgEdgeKind<'tcx>>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) {
        pcg_validity_assert!(
            from.is_disjoint(to),
            "Non-disjoint edges: {} and {}",
            from.to_short_string(ctxt),
            to.to_short_string(ctxt)
        );
        self.add_edge(from, to, weight);
    }

    pub(crate) fn transitive_reduction(
        &mut self,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> FxHashSet<&'graph BorrowPcgEdgeKind<'tcx>> {
        pcg_validity_assert!(
            self.is_acyclic(),
            "Graph contains cycles after SCC computation"
        );

        tracing::info!("Before");
        if validity_checks_enabled() {
            for (source, target, _) in self.edges() {
                pcg_validity_assert!(
                    source.is_disjoint(&target),
                    "Non-disjoint edges: {} and {}",
                    source.to_short_string(ctxt),
                    target.to_short_string(ctxt)
                );
            }
        }
        tracing::info!("After");

        let toposort = petgraph::algo::toposort(&self.inner(), None).unwrap();
        let (g, revmap) =
            petgraph::algo::tred::dag_to_toposorted_adjacency_list(&self.inner(), &toposort);

        let (tred, _) = petgraph::algo::tred::dag_transitive_reduction_closure::<_, u32>(&g);
        let mut removed_edges = FxHashSet::default();
        self.retain_edges(|slf, ei| {
            let endpoints = slf.edge_endpoints(ei).unwrap();
            let should_keep =
                tred.contains_edge(revmap[endpoints.0.index()], revmap[endpoints.1.index()]);
            if !should_keep {
                let from_node = slf.node_weight(endpoints.0).unwrap();
                let to_node = slf.node_weight(endpoints.1).unwrap();
                tracing::debug!(
                    "Removing edge {} -> {} because of transitive reduction",
                    from_node.to_short_string(ctxt),
                    to_node.to_short_string(ctxt)
                );
                removed_edges.extend(slf.edge_weight(ei).unwrap().clone());
            }
            should_keep
        });
        if validity_checks_enabled() {
            for (source, target, _) in self.edges() {
                pcg_validity_assert!(
                    source.is_disjoint(&target),
                    "Non-disjoint edges: {} and {}",
                    source.to_short_string(ctxt),
                    target.to_short_string(ctxt)
                );
            }
        }
        removed_edges
    }
    pub(crate) fn merge(&mut self, other: &Self, ctxt: CompilerCtxt<'_, 'tcx>) {
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

        if validity_checks_enabled() {
            for (source, target, _) in self.edges() {
                pcg_validity_assert!(
                    source.is_disjoint(&target),
                    "Non-disjoint edges: {} and {}",
                    source.to_short_string(ctxt),
                    target.to_short_string(ctxt)
                );
            }
        }

        'top: loop {
            for blocked in self.inner().node_indices() {
                for blocking in self.inner().node_indices() {
                    if has_path_connecting(&self.inner(), blocked, blocking, None) {
                        continue;
                    }
                    let blocked_data = self.inner().node_weight(blocked).unwrap();
                    let blocking_data = self.inner().node_weight(blocking).unwrap();
                    if let Some(blocked_region) = blocked_data.nodes.region_repr(ctxt)
                        && let Some(blocking_region) = blocking_data.nodes.region_repr(ctxt)
                        && !blocking_data.nodes.is_remote()
                        && ctxt.bc.outlives(blocked_region, blocking_region)
                    // && !ctxt.bc.outlives(blocking_region, blocked_region) // TODO: We don't want this
                    {

                        tracing::info!(
                            "Adding edge {} -> {} because of outlives",
                            blocked_data.to_short_string(ctxt),
                            blocking_data.to_short_string(ctxt)
                        );
                        if coupling_imgcat_debug() {
                            self.render_with_imgcat(ctxt, "Before add");
                        }
                        match self.add_edge_via_indices(blocked, blocking, Default::default())
                        {
                            AddEdgeResult::DidNotMergeNodes => {
                                tracing::info!("No merge");
                                let edges = self.transitive_reduction(ctxt);
                                self.update_inner_edge(blocked, blocking, edges);
                                if coupling_imgcat_debug() {
                                    self.render_with_imgcat(ctxt, "Post add");
                                }
                            }
                            AddEdgeResult::MergedNodes => {
                                tracing::info!("Merged");
                                if coupling_imgcat_debug() {
                                    self.render_with_imgcat(ctxt, "Post add");
                                }
                                continue 'top;
                            }
                        }
                    }
                }
            }
            tracing::info!("After top");
            pcg_validity_assert!(self.is_acyclic(), "Resulting graph contains cycles");
            return;
        }
    }
}

impl<T: Clone> Coupled<T> {
    pub fn size(&self) -> usize {
        self.0.len()
    }

    pub fn singleton(item: T) -> Self {
        let mut sv = SmallVec::new();
        sv.push(item);
        Self(sv)
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.0.iter()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut T> {
        self.0.iter_mut()
    }
}

impl<T> IntoIterator for Coupled<T> {
    type Item = T;
    type IntoIter = <SmallVec<[T; 4]> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<T: Ord> Coupled<T> {
    pub fn elems_btree_set(&self) -> BTreeSet<&T> {
        self.0.iter().collect()
    }

    pub fn contains(&self, item: &T) -> bool {
        self.0.contains(item)
    }
}

impl<T> From<BTreeSet<T>> for Coupled<T> {
    fn from(set: BTreeSet<T>) -> Self {
        Self(set.into_iter().collect())
    }
}

impl<T: Ord> From<Vec<T>> for Coupled<T> {
    fn from(vec: Vec<T>) -> Self {
        let mut bts = BTreeSet::new();
        for item in vec {
            bts.insert(item);
        }
        Self(bts.into_iter().collect())
    }
}

/// Records a history of actions for debugging purpose;
/// used to detect infinite recursion
#[derive(Clone)]
struct DebugRecursiveCallHistory<T> {
    #[cfg(debug_assertions)]
    history: Vec<T>,
    #[cfg(not(debug_assertions))]
    _marker: std::marker::PhantomData<T>,
}

#[cfg(debug_assertions)]
impl<'tcx, T: DisplayWithCompilerCtxt<'tcx>> DebugRecursiveCallHistory<T> {
    fn new() -> Self {
        Self { history: vec![] }
    }

    fn add(&mut self, action: T, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String>
    where
        T: std::cmp::Eq + std::fmt::Display,
    {
        if self.history.contains(&action) {
            return Err(format!(
                "Infinite recursion adding:\n{}, to path:\n{}",
                action.to_short_string(ctxt),
                self.history
                    .iter()
                    .map(|a| a.to_short_string(ctxt))
                    .collect::<Vec<_>>()
                    .join("\n")
            ));
        }
        self.history.push(action);
        Ok(())
    }
}

#[cfg(not(debug_assertions))]
impl<T> DebugRecursiveCallHistory<T> {
    fn new() -> Self {
        Self {
            _marker: std::marker::PhantomData,
        }
    }

    fn add(&mut self, _action: T, _ctxt: CompilerCtxt<'_, '_>) -> Result<(), String> {
        Ok(())
    }
}

pub(crate) struct AbstractionGraphConstructor<'mir, 'tcx, 'graph> {
    ctxt: CompilerCtxt<'mir, 'tcx>,
    loop_head_block: BasicBlock,
    graph: AbstractionGraph<'tcx, 'graph>,
}

#[derive(Clone, Eq, PartialEq)]
struct AddEdgeHistory<'a, 'tcx> {
    bottom_connect: &'a Coupled<AbstractionGraphNode<'tcx>>,
    upper_candidate: &'a Coupled<AbstractionGraphNode<'tcx>>,
}

impl<'tcx> DisplayWithCompilerCtxt<'tcx> for AddEdgeHistory<'_, 'tcx> {
    fn to_short_string(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> String {
        format!(
            "bottom: {{{}}}, upper: {{{}}}",
            self.bottom_connect.to_short_string(ctxt),
            self.upper_candidate.to_short_string(ctxt)
        )
    }
}
impl std::fmt::Display for AddEdgeHistory<'_, '_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "bottom: {{{}}}, upper: {{{}}}",
            self.bottom_connect
                .iter()
                .map(|x| format!("{x:?}"))
                .collect::<Vec<_>>()
                .join(", "),
            self.upper_candidate
                .iter()
                .map(|x| format!("{x:?}"))
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

impl<'mir: 'graph, 'tcx, 'graph> AbstractionGraphConstructor<'mir, 'tcx, 'graph> {
    pub(crate) fn new(ctxt: CompilerCtxt<'mir, 'tcx>, loop_head_block: BasicBlock) -> Self {
        Self {
            ctxt,
            loop_head_block,
            graph: AbstractionGraph::new(),
        }
    }

    fn add_edges_from<'a>(
        &mut self,
        bg: &AbstractionGraph<'tcx, 'graph>,
        bottom_connect: &'a Coupled<AbstractionGraphNode<'tcx>>,
        upper_candidate: &'a Coupled<AbstractionGraphNode<'tcx>>,
        incoming_weight: FxHashSet<&'graph BorrowPcgEdgeKind<'tcx>>,
        borrow_checker: &dyn BorrowCheckerInterface<'tcx>,
        mut history: DebugRecursiveCallHistory<AddEdgeHistory<'a, 'tcx>>,
    ) {
        if let Err(e) = history.add(
            AddEdgeHistory {
                bottom_connect,
                upper_candidate,
            },
            self.ctxt,
        ) {
            panic!("Infinite recursion adding edge: {e}");
        }
        let upper_candidate = upper_candidate.clone();
        let endpoints = bg.parents(&upper_candidate);
        for (coupled, edge_weight) in endpoints {
            let mut weight = incoming_weight.clone();
            weight.extend(edge_weight);
            pcg_validity_assert!(
                coupled != upper_candidate,
                "Coupling graph should be acyclic"
            );
            let is_root = bg.is_root(&coupled) && !coupled.iter().any(|n| n.is_old());
            let should_include = is_root
                || coupled.iter().any(|n| {
                    let is_live = borrow_checker.is_live(
                        (*n).to_pcg_node().into(),
                        Location {
                            block: self.loop_head_block,
                            statement_index: 0,
                        },
                        false, // TODO: Maybe actually check if this is a leaf
                    );
                    is_live && !n.is_old()
                });
            if !should_include {
                self.add_edges_from(
                    bg,
                    bottom_connect,
                    &coupled,
                    weight.clone(),
                    borrow_checker,
                    history.clone(),
                );
            } else {
                self.graph
                    .add_edge_with_ctxt(&coupled, &bottom_connect.clone(), weight.clone(), self.ctxt);
                self.add_edges_from(
                    bg,
                    &coupled,
                    &coupled,
                    FxHashSet::default(),
                    borrow_checker,
                    history.clone(),
                );
            }
        }
    }

    pub(crate) fn construct_abstraction_graph(
        mut self,
        bg: &'graph BorrowsGraph<'tcx>,
        borrow_checker: &dyn BorrowCheckerInterface<'tcx>,
    ) -> AbstractionGraph<'tcx, 'graph> {
        tracing::debug!("Construct abstraction graph start");
        let full_graph = bg.base_abstraction_graph(self.loop_head_block, self.ctxt);
        if coupling_imgcat_debug() {
            full_graph.render_with_imgcat(self.ctxt, "Base abstraction graph");
        }
        let leaf_nodes = full_graph.leaf_nodes();
        let num_leaf_nodes = leaf_nodes.len();
        for (i, node) in leaf_nodes.into_iter().enumerate() {
            tracing::debug!("Inserting leaf node {} / {}", i, num_leaf_nodes);
            self.graph.insert_endpoint(node.clone());
            self.add_edges_from(
                &full_graph,
                &node,
                &node,
                FxHashSet::default(),
                borrow_checker,
                DebugRecursiveCallHistory::new(),
            );
        }
        tracing::debug!("Construct coupling graph end");
        self.graph.mut_leaf_nodes(|node| {
            node.nodes.mutate(|n| {
                n.remove_rp_label_if_present();
            });
        });
        self.graph
    }
}
