use std::cell::{Ref, RefCell};

use derive_more::{Deref, IntoIterator};

use crate::{
    borrow_pcg::{
        borrow_pcg_edge::{BorrowPCGEdgeRef, LocalNode},
        edge_data::EdgeData,
    },
    pcg::PCGNode,
    rustc_interface::
        data_structures::fx::{FxHashMap, FxHashSet}
    ,
    utils::CompilerCtxt,
};

use super::BorrowsGraph;

#[derive(Deref, Clone, IntoIterator)]
pub struct CachedBlockingEdges<'graph, 'tcx>(Vec<BorrowPCGEdgeRef<'tcx, 'graph>>);

impl<'graph, 'tcx> CachedBlockingEdges<'graph, 'tcx> {
    fn new(edges: Vec<BorrowPCGEdgeRef<'tcx, 'graph>>) -> Self {
        Self(edges)
    }
}

type CachedBlockedEdges<'graph, 'tcx> = Vec<BorrowPCGEdgeRef<'tcx, 'graph>>;
pub(crate) type CachedLeafEdges<'graph, 'tcx> = Vec<BorrowPCGEdgeRef<'tcx, 'graph>>;

pub struct FrozenGraphRef<'graph, 'tcx> {
    graph: &'graph BorrowsGraph<'tcx>,
    nodes_cache: RefCell<Option<FxHashSet<PCGNode<'tcx>>>>,
    edges_blocking_cache: RefCell<FxHashMap<PCGNode<'tcx>, CachedBlockingEdges<'graph, 'tcx>>>,
    edges_blocked_by_cache: RefCell<FxHashMap<LocalNode<'tcx>, CachedBlockedEdges<'graph, 'tcx>>>,
    leaf_edges_cache: RefCell<Option<CachedLeafEdges<'graph, 'tcx>>>,
    roots_cache: RefCell<Option<FxHashSet<PCGNode<'tcx>>>>,
}

impl<'graph, 'tcx> FrozenGraphRef<'graph, 'tcx> {
    pub(crate) fn new(graph: &'graph BorrowsGraph<'tcx>) -> Self {
        Self {
            graph,
            nodes_cache: RefCell::new(None),
            edges_blocking_cache: RefCell::new(FxHashMap::default()),
            edges_blocked_by_cache: RefCell::new(FxHashMap::default()),
            leaf_edges_cache: RefCell::new(None),
            roots_cache: RefCell::new(None),
        }
    }

    pub fn contains(&self, node: PCGNode<'tcx>, repacker: CompilerCtxt<'_, 'tcx>) -> bool {
        self.nodes(repacker).contains(&node)
    }

    pub fn nodes<'slf>(
        &'slf self,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> Ref<'slf, FxHashSet<PCGNode<'tcx>>> {
        {
            let nodes = self.nodes_cache.borrow();
            if nodes.is_some() {
                return Ref::map(nodes, |o| o.as_ref().unwrap());
            }
        }
        let nodes = self.graph.nodes(repacker);
        self.nodes_cache.replace(Some(nodes));
        Ref::map(self.nodes_cache.borrow(), |o| o.as_ref().unwrap())
    }

    pub fn roots<'slf, 'bc: 'graph, C: Copy>(
        &'slf self,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> Ref<'slf, FxHashSet<PCGNode<'tcx>>> {
        {
            let roots = self.roots_cache.borrow();
            if roots.is_some() {
                return Ref::map(roots, |o| o.as_ref().unwrap());
            }
        }
        let roots = self.graph.roots(repacker);
        self.roots_cache.replace(Some(roots));
        Ref::map(self.roots_cache.borrow(), |o| o.as_ref().unwrap())
    }

    pub fn leaf_edges<'slf, 'mir: 'graph, 'bc: 'graph>(
        &'slf self,
        repacker: CompilerCtxt<'mir, 'tcx>,
    ) -> CachedLeafEdges<'graph, 'tcx> {
        {
            let edges = self.leaf_edges_cache.borrow();
            if edges.is_some() {
                return edges.as_ref().unwrap().clone();
            }
        }
        let edges: CachedLeafEdges<'graph, 'tcx> = self.graph.leaf_edges_set(repacker, Some(self));
        self.leaf_edges_cache.replace(Some(edges.clone()));
        edges
    }

    pub fn leaf_nodes<'slf, 'mir: 'graph, 'bc: 'graph>(
        &'slf self,
        repacker: CompilerCtxt<'mir, 'tcx>,
    ) -> impl Iterator<Item = LocalNode<'tcx>> + use<'tcx, 'slf, 'mir, 'bc> {
        self.leaf_edges(repacker)
            .into_iter()
            .flat_map(move |edge| edge.blocked_by_nodes(repacker).collect::<Vec<_>>())
    }

    pub fn get_edges_blocked_by<'mir: 'graph, 'bc: 'graph, C: Copy>(
        &mut self,
        node: LocalNode<'tcx>,
        ctxt: CompilerCtxt<'mir, 'tcx, C>,
    ) -> &CachedBlockedEdges<'graph, 'tcx> {
        self.edges_blocked_by_cache
            .get_mut()
            .entry(node)
            .or_insert_with(|| self.graph.edges_blocked_by(node, ctxt).collect())
    }

    pub fn get_edges_blocking<'slf, 'mir: 'graph, 'bc: 'graph, C: Copy>(
        &'slf self,
        node: PCGNode<'tcx>,
        repacker: CompilerCtxt<'mir, 'tcx, C>,
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

    pub fn has_edge_blocking<'mir: 'graph, 'bc: 'graph>(
        &self,
        node: PCGNode<'tcx>,
        repacker: CompilerCtxt<'mir, 'tcx>,
    ) -> bool {
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
