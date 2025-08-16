use std::cell::{Ref, RefCell};

use derive_more::{Deref, IntoIterator};
use itertools::Itertools;

use crate::{
    borrow_pcg::{
        borrow_pcg_edge::{BorrowPcgEdgeRef, LocalNode},
        edge_data::EdgeData,
    },
    pcg::{PCGNodeLike, PcgNode},
    rustc_interface::data_structures::fx::{FxHashMap, FxHashSet},
    utils::{
        CompilerCtxt, HasBorrowCheckerCtxt, HasCompilerCtxt, display::DisplayWithCompilerCtxt,
    },
};

use super::BorrowsGraph;

#[derive(Deref, Clone, IntoIterator)]
pub struct CachedBlockingEdges<'graph, 'tcx>(Vec<BorrowPcgEdgeRef<'tcx, 'graph>>);

impl<'graph, 'tcx> CachedBlockingEdges<'graph, 'tcx> {
    fn new(edges: Vec<BorrowPcgEdgeRef<'tcx, 'graph>>) -> Self {
        Self(edges)
    }
}

pub(crate) type CachedLeafEdges<'graph, 'tcx> = Vec<BorrowPcgEdgeRef<'tcx, 'graph>>;

/// A data structure used for querying the Borrow PCG
///
/// It contains a reference to a Borrow PCG and mutable data structures for
/// caching intermediate query results.
pub struct FrozenGraphRef<'graph, 'tcx> {
    graph: &'graph BorrowsGraph<'tcx>,
    nodes_cache: RefCell<Option<FxHashSet<PcgNode<'tcx>>>>,
    edges_blocking_cache: RefCell<FxHashMap<PcgNode<'tcx>, CachedBlockingEdges<'graph, 'tcx>>>,
    leaf_edges_cache: RefCell<Option<CachedLeafEdges<'graph, 'tcx>>>,
    roots_cache: RefCell<Option<FxHashSet<PcgNode<'tcx>>>>,
}

impl<'graph, 'tcx> FrozenGraphRef<'graph, 'tcx> {
    pub(crate) fn new(graph: &'graph BorrowsGraph<'tcx>) -> Self {
        Self {
            graph,
            nodes_cache: RefCell::new(None),
            edges_blocking_cache: RefCell::new(FxHashMap::default()),
            leaf_edges_cache: RefCell::new(None),
            roots_cache: RefCell::new(None),
        }
    }

    pub(crate) fn is_acyclic<'mir: 'graph, 'bc: 'graph>(
        &mut self,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> bool {
        enum PushResult<'tcx, 'graph> {
            ExtendPath(Path<'tcx, 'graph>),
            Cycle,
        }

        #[derive(Clone, Debug, Eq, PartialEq, Hash)]
        struct Path<'tcx, 'graph>(Vec<BorrowPcgEdgeRef<'tcx, 'graph>>);

        impl<'tcx, 'graph> Path<'tcx, 'graph> {
            fn try_push(
                mut self,
                edge: BorrowPcgEdgeRef<'tcx, 'graph>,
                _ctxt: CompilerCtxt<'_, 'tcx>,
            ) -> PushResult<'tcx, 'graph> {
                if self.0.contains(&edge) {
                    PushResult::Cycle
                } else {
                    self.0.push(edge);
                    PushResult::ExtendPath(self)
                }
            }

            fn last(&self) -> BorrowPcgEdgeRef<'tcx, 'graph> {
                *self.0.last().unwrap()
            }

            fn new(edge: BorrowPcgEdgeRef<'tcx, 'graph>) -> Self {
                Self(vec![edge])
            }

            #[must_use]
            fn leads_to_cycle<'mir: 'graph, 'bc: 'graph>(
                &self,
                graph: &FrozenGraphRef<'graph, 'tcx>,
                ctxt: CompilerCtxt<'mir, 'tcx>,
            ) -> bool {
                let curr = self.last();
                let blocking_edges = curr
                    .blocked_by_nodes(ctxt)
                    .flat_map(|node| graph.get_edges_blocking(node.into(), ctxt))
                    .unique();
                for edge in blocking_edges {
                    match self.clone().try_push(edge, ctxt) {
                        PushResult::Cycle => {
                            tracing::info!("Cycle: {}", self.0.to_short_string(ctxt));
                            return true;
                        }
                        PushResult::ExtendPath(next_path) => {
                            if next_path.leads_to_cycle(graph, ctxt) {
                                return true;
                            }
                        }
                    }
                }
                false
            }
        }

        for node in self.nodes(ctxt).iter() {
            for edge in self.get_edges_blocking(*node, ctxt) {
                if Path::new(edge).leads_to_cycle(self, ctxt) {
                    return false;
                }
            }
        }

        true
    }

    pub fn nodes<'slf, 'a: 'graph>(
        &'slf self,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Ref<'slf, FxHashSet<PcgNode<'tcx>>>
    where
        'tcx: 'a,
    {
        {
            let nodes = self.nodes_cache.borrow();
            if nodes.is_some() {
                return Ref::map(nodes, |o| o.as_ref().unwrap());
            }
        }
        let nodes = self.graph.nodes(ctxt);
        self.nodes_cache.replace(Some(nodes));
        Ref::map(self.nodes_cache.borrow(), |o| o.as_ref().unwrap())
    }

    pub fn roots<'slf, 'bc: 'graph>(
        &'slf self,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Ref<'slf, FxHashSet<PcgNode<'tcx>>> {
        {
            let roots = self.roots_cache.borrow();
            if roots.is_some() {
                return Ref::map(roots, |o| o.as_ref().unwrap());
            }
        }
        let roots = self.graph.roots(ctxt);
        self.roots_cache.replace(Some(roots));
        Ref::map(self.roots_cache.borrow(), |o| o.as_ref().unwrap())
    }

    pub fn leaf_edges<'slf, 'a: 'graph, 'bc: 'graph>(
        &'slf self,
        repacker: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> CachedLeafEdges<'graph, 'tcx>
    where
        'tcx: 'a,
    {
        {
            let edges = self.leaf_edges_cache.borrow();
            if edges.is_some() {
                return edges.as_ref().unwrap().clone();
            }
        }
        let edges: CachedLeafEdges<'graph, 'tcx> = self.graph.leaf_edges_set(repacker, self);
        self.leaf_edges_cache.replace(Some(edges.clone()));
        edges
    }

    pub fn leaf_nodes<'slf, 'a: 'graph>(
        &'slf self,
        repacker: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Vec<LocalNode<'tcx>>
    where
        'tcx: 'a,
    {
        self.nodes(repacker)
            .iter()
            .filter_map(|node| node.try_to_local_node(repacker))
            .filter(|node| self.is_leaf(*node, repacker))
            .collect()
    }

    pub(crate) fn is_leaf<'slf, 'a: 'graph>(
        &'slf self,
        node: LocalNode<'tcx>,
        repacker: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> bool
    where
        'tcx: 'a,
    {
        self.graph
            .edges()
            .all(|edge| !edge.blocks_node(node.into(), repacker.bc_ctxt()))
    }

    pub fn get_edges_blocking<'slf, 'mir: 'graph, 'bc: 'graph>(
        &'slf self,
        node: PcgNode<'tcx>,
        repacker: CompilerCtxt<'mir, 'tcx>,
    ) -> CachedBlockingEdges<'graph, 'tcx> {
        {
            let map = self.edges_blocking_cache.borrow();
            if map.contains_key(&node) {
                return map[&node].clone();
            }
        }
        let edges = CachedBlockingEdges::new(self.graph.edges_blocking_set(node, repacker));
        self.edges_blocking_cache
            .borrow_mut()
            .insert(node, edges.clone());
        edges
    }

    pub fn has_edge_blocking<'slf, 'a: 'graph, 'bc: 'graph>(
        &'slf self,
        node: PcgNode<'tcx>,
        repacker: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> bool
    where
        'tcx: 'a,
    {
        {
            let map = self.edges_blocking_cache.borrow();
            if map.contains_key(&node) {
                return !map[&node].is_empty();
            }
        }
        let edges = CachedBlockingEdges::new(self.graph.edges_blocking_set(node, repacker));
        let result = !edges.is_empty();
        self.edges_blocking_cache.borrow_mut().insert(node, edges);
        result
    }
}
