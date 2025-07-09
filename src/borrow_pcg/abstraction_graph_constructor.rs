use petgraph::algo::has_path_connecting;

use super::{
    edge::kind::BorrowPcgEdgeKind,
    graph::{coupling_imgcat_debug, BorrowsGraph},
    region_projection::PcgRegion,
};
use crate::{
    borrow_checker::BorrowCheckerInterface,
    borrow_pcg::abstraction::node::AbstractionGraphNode,
    coupling::{coupled::Coupled, AddEdgeResult, NodeData},
    utils::{data_structures::HashSet},
    validity_checks_enabled,
};
use crate::{
    coupling,
    pcg::PCGNode,
    pcg_validity_assert,
    rustc_interface::data_structures::fx::FxHashSet,
    rustc_interface::middle::mir::{BasicBlock, Location},
    utils::{display::DisplayWithCompilerCtxt, CompilerCtxt},
};

#[derive(Clone)]
pub(crate) struct AbstractionGraph<'tcx> {
    inner: coupling::DisjointSetGraph<AbstractionGraphNode<'tcx>, BorrowPcgEdgeKind<'tcx>>,
}

impl<'tcx> Coupled<AbstractionGraphNode<'tcx>> {
    pub(crate) fn region_repr(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Option<PcgRegion> {
        self.iter().find_map(|n| match n.to_pcg_node(ctxt) {
            PCGNode::RegionProjection(rp) => Some(rp.region(ctxt)),
            _ => None,
        })
    }

    pub(crate) fn is_remote(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        self.iter().any(|n| match n.to_pcg_node(ctxt) {
            PCGNode::Place(p) => p.is_remote(),
            PCGNode::RegionProjection(rp) => rp.is_remote(ctxt),
        })
    }
}

impl<'tcx> AbstractionGraph<'tcx> {
    pub(crate) fn new() -> Self {
        Self {
            inner: coupling::DisjointSetGraph::new(),
        }
    }

    pub(crate) fn nodes(&self) -> Vec<Coupled<AbstractionGraphNode<'tcx>>> {
        self.inner.nodes()
    }

    pub(crate) fn mut_non_leaf_nodes(
        &mut self,
        f: impl FnMut(&mut NodeData<AbstractionGraphNode<'tcx>, BorrowPcgEdgeKind<'tcx>>),
    ) {
        self.inner.mut_non_leaf_nodes(f);
    }

    pub(crate) fn render_with_imgcat(&self, ctxt: CompilerCtxt<'_, 'tcx>, comment: &str) {
        self.inner.render_with_imgcat(ctxt, comment);
    }

    pub(crate) fn edges(
        &self,
    ) -> impl Iterator<
        Item = (
            Coupled<AbstractionGraphNode<'tcx>>,
            Coupled<AbstractionGraphNode<'tcx>>,
            FxHashSet<BorrowPcgEdgeKind<'tcx>>,
        ),
    > + '_ {
        self.inner.edges()
    }

    pub(crate) fn add_edge(
        &mut self,
        from: &Coupled<AbstractionGraphNode<'tcx>>,
        to: &Coupled<AbstractionGraphNode<'tcx>>,
        weight: HashSet<BorrowPcgEdgeKind<'tcx>>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) {
        pcg_validity_assert!(
            from.is_disjoint(to),
            "Non-disjoint edges: {} and {}",
            from.to_short_string(ctxt),
            to.to_short_string(ctxt)
        );
        self.inner.add_edge(from, to, weight);
    }

    pub(crate) fn transitive_reduction(
        &mut self,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> FxHashSet<BorrowPcgEdgeKind<'tcx>> {
        pcg_validity_assert!(
            self.inner.is_acyclic(),
            "Graph contains cycles after SCC computation"
        );

        if validity_checks_enabled() {
            for (source, target, _) in self.inner.edges() {
                pcg_validity_assert!(
                    source.is_disjoint(&target),
                    "Non-disjoint edges: {} and {}",
                    source.to_short_string(ctxt),
                    target.to_short_string(ctxt)
                );
            }
        }

        let toposort = petgraph::algo::toposort(&self.inner.inner(), None).unwrap();
        let (g, revmap) =
            petgraph::algo::tred::dag_to_toposorted_adjacency_list(&self.inner.inner(), &toposort);

        let (tred, _) = petgraph::algo::tred::dag_transitive_reduction_closure::<_, u32>(&g);
        let mut removed_edges = FxHashSet::default();
        self.inner.retain_edges(|slf, ei| {
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
            for (source, target, _) in self.inner.edges() {
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
    pub(crate) fn merge(
        &mut self,
        other: &Self,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) {
        self.inner.join(&other.inner);
        if validity_checks_enabled() {
            for (source, target, _) in self.inner.edges() {
                pcg_validity_assert!(
                    source.is_disjoint(&target),
                    "Non-disjoint edges: {} and {}",
                    source.to_short_string(ctxt),
                    target.to_short_string(ctxt)
                );
            }
        }

        if coupling_imgcat_debug() {
            self.inner.render_with_imgcat(ctxt, "After base merge");
        }

        'top: loop {
            for blocked in self.inner.inner().node_indices() {
                for blocking in self.inner.inner().node_indices() {
                    if has_path_connecting(&self.inner.inner(), blocked, blocking, None) {
                        continue;
                    }
                    let blocked_data = self.inner.inner().node_weight(blocked).unwrap();
                    let blocking_data = self.inner.inner().node_weight(blocking).unwrap();
                    // if !blocking_data
                    //     .nodes
                    //     .iter()
                    //     .flat_map(|n| n.related_current_place())
                    //     .any(|p| loop_usage.used_in_loop(p, ctxt))
                    // {
                    //     continue;
                    // }
                    if let Some(blocked_region) = blocked_data.nodes.region_repr(ctxt)
                        && let Some(blocking_region) = blocking_data.nodes.region_repr(ctxt)
                        && !blocking_data.nodes.is_remote(ctxt)
                        && ctxt.bc.outlives(blocked_region, blocking_region)
                    // && !ctxt.bc.outlives(blocking_region, blocked_region) // TODO: We don't want this
                    {
                        tracing::debug!(
                            "Adding edge {} -> {} because of outlives",
                            blocked_data.to_short_string(ctxt),
                            blocking_data.to_short_string(ctxt)
                        );
                        match self
                            .inner
                            .add_edge_via_indices(blocked, blocking, Default::default())
                        {
                            AddEdgeResult::DidNotMergeNodes => {
                                let edges = self.transitive_reduction(ctxt);
                                self.inner.update_inner_edge(blocked, blocking, edges);
                            }
                            AddEdgeResult::MergedNodes => {
                                continue 'top;
                            }
                        }
                    }
                }
            }
            pcg_validity_assert!(self.inner.is_acyclic(), "Resulting graph contains cycles");
            return;
        }
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
impl<'tcx, T> DebugRecursiveCallHistory<T> {
    fn new() -> Self {
        Self { history: vec![] }
    }

    fn add<BC: Copy>(&mut self, action: T, ctxt: CompilerCtxt<'_, 'tcx, BC>) -> Result<(), String>
    where
        T: std::cmp::Eq + std::fmt::Display + DisplayWithCompilerCtxt<'tcx, BC>,
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

pub(crate) struct AbstractionGraphConstructor<'mir, 'tcx> {
    ctxt: CompilerCtxt<'mir, 'tcx>,
    loop_head_block: BasicBlock,
    graph: AbstractionGraph<'tcx>,
}

#[derive(Clone, Eq, PartialEq)]
struct AddEdgeHistory<'a, 'tcx> {
    bottom_connect: &'a Coupled<AbstractionGraphNode<'tcx>>,
    upper_candidate: &'a Coupled<AbstractionGraphNode<'tcx>>,
}

impl<'tcx, 'a> DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>
    for AddEdgeHistory<'_, 'tcx>
{
    fn to_short_string(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    ) -> String {
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

impl<'mir, 'tcx> AbstractionGraphConstructor<'mir, 'tcx> {
    pub(crate) fn new(ctxt: CompilerCtxt<'mir, 'tcx>, loop_head_block: BasicBlock) -> Self {
        Self {
            ctxt,
            loop_head_block,
            graph: AbstractionGraph {
                inner: coupling::DisjointSetGraph::new(),
            },
        }
    }

    fn add_edges_from<'a>(
        &mut self,
        origin_graph: &BorrowsGraph<'tcx>,
        bg: &AbstractionGraph<'tcx>,
        bottom_connect: &'a Coupled<AbstractionGraphNode<'tcx>>,
        upper_candidate: &'a Coupled<AbstractionGraphNode<'tcx>>,
        incoming_weight: FxHashSet<BorrowPcgEdgeKind<'tcx>>,
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
        let endpoints = bg.inner.parents(&upper_candidate);

        for (coupled, edge_weight) in endpoints {
            let mut weight = incoming_weight.clone();
            weight.extend(edge_weight);
            pcg_validity_assert!(
                coupled != upper_candidate,
                "Coupling graph should be acyclic"
            );
            let in_origin = coupled
                .iter()
                .all(|n| origin_graph.contains(n.to_pcg_node(self.ctxt), self.ctxt));
            let is_root = bg.inner.is_root(&coupled);
            let should_include = in_origin
                && (is_root
                    || coupled.iter().any(|n| {
                        let is_live = borrow_checker.is_live(
                            (*n).to_pcg_node(self.ctxt),
                            Location {
                                block: self.loop_head_block,
                                statement_index: 0,
                            },
                        );
                        is_live && !n.is_old()
                    }));
            if !should_include {
                self.add_edges_from(
                    origin_graph,
                    bg,
                    bottom_connect,
                    &coupled,
                    weight.clone(),
                    borrow_checker,
                    history.clone(),
                );
            } else {
                self.graph.add_edge(
                    &without_old(&coupled),
                    &without_old(bottom_connect),
                    weight.clone(),
                    self.ctxt,
                );
                self.add_edges_from(
                    origin_graph,
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

    pub(crate) fn remove_intermediate_nodes(
        mut self,
        origin_graph: &BorrowsGraph<'tcx>,
        full_graph: AbstractionGraph<'tcx>,
        borrow_checker: &dyn BorrowCheckerInterface<'tcx>,
    ) -> AbstractionGraph<'tcx> {
        if coupling_imgcat_debug() {
            full_graph
                .inner
                .render_with_imgcat(self.ctxt, "Base abstraction graph");
        }
        let leaf_nodes = full_graph.inner.leaf_nodes();
        let num_leaf_nodes = leaf_nodes.len();
        for (i, node) in leaf_nodes.into_iter().enumerate() {
            tracing::debug!("Inserting leaf node {} / {}", i, num_leaf_nodes);
            self.graph.inner.insert_endpoint(without_old(&node));
            self.add_edges_from(
                origin_graph,
                &full_graph,
                &node,
                &node,
                HashSet::default(),
                borrow_checker,
                DebugRecursiveCallHistory::new(),
            );
        }
        tracing::debug!("Construct coupling graph end");
        self.graph.inner.mut_leaf_nodes(|node| {
            node.nodes.mutate(|n| {
                n.remove_rp_label_if_present();
            });
        });
        self.graph
    }
}

fn without_old<'tcx>(
    coupled: &Coupled<AbstractionGraphNode<'tcx>>,
) -> Coupled<AbstractionGraphNode<'tcx>> {
    // TODO: What if all nodes are old?
    coupled
        .clone()
        .retain(|n| !n.is_old())
        .unwrap_or_else(|| coupled.clone())
}
