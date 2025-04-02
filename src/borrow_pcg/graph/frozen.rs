use std::cell::{Ref, RefCell};

use derive_more::IntoIterator;
use itertools::Itertools;

use crate::{
    borrow_pcg::{
        borrow_pcg_edge::{BorrowPCGEdgeLike, BorrowPCGEdgeRef, LocalNode},
        coupling_graph_constructor::BorrowCheckerInterface,
        edge::{kind::BorrowPCGEdgeKind, outlives::OutlivesEdgeKind},
        edge_data::EdgeData,
        path_condition::PathConditions,
        region_projection::{LocalRegionProjection, RegionProjection},
    },
    pcg::{LocalNodeLike, PCGNode, PCGNodeLike},
    rustc_interface::{
        data_structures::fx::{FxHashMap, FxHashSet},
        middle::mir::TerminatorEdges,
    },
    utils::PlaceRepacker,
};

use super::BorrowsGraph;

#[derive(Clone, IntoIterator)]
pub struct CachedBlockingEdges<'graph, 'tcx>(Vec<BorrowPCGEdgeRef<'tcx, 'graph>>);

impl<'graph, 'tcx> CachedBlockingEdges<'graph, 'tcx> {
    fn new(edges: Vec<BorrowPCGEdgeRef<'tcx, 'graph>>) -> Self {
        Self(edges)
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
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

    pub fn contains(&self, node: PCGNode<'tcx>, repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        self.nodes(repacker).contains(&node)
    }

    pub fn nodes<'slf>(
        &'slf self,
        repacker: PlaceRepacker<'_, 'tcx>,
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

    pub fn roots<'slf>(
        &'slf self,
        repacker: PlaceRepacker<'_, 'tcx>,
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

    pub fn leaf_edges<'slf, 'mir: 'graph>(
        &'slf self,
        repacker: PlaceRepacker<'mir, 'tcx>,
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

    pub fn leaf_nodes<'slf, 'mir: 'graph>(
        &'slf self,
        repacker: PlaceRepacker<'mir, 'tcx>,
    ) -> impl Iterator<Item = LocalNode<'tcx>> + 'slf {
        self.leaf_edges(repacker)
            .into_iter()
            .flat_map(move |edge| edge.blocked_by_nodes(repacker))
    }

    pub fn get_edges_blocked_by<'mir: 'graph>(
        &mut self,
        node: LocalNode<'tcx>,
        repacker: PlaceRepacker<'mir, 'tcx>,
    ) -> &CachedBlockedEdges<'graph, 'tcx> {
        self.edges_blocked_by_cache
            .get_mut()
            .entry(node)
            .or_insert_with(|| self.graph.edges_blocked_by(node, repacker).collect())
    }

    pub fn get_edges_blocking<'slf, 'mir: 'graph>(
        &'slf self,
        node: PCGNode<'tcx>,
        repacker: PlaceRepacker<'mir, 'tcx>,
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

    pub fn has_edge_blocking<'mir: 'graph>(
        &self,
        node: PCGNode<'tcx>,
        repacker: PlaceRepacker<'mir, 'tcx>,
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

    pub(super) fn is_acyclic<'mir: 'graph>(&mut self, repacker: PlaceRepacker<'mir, 'tcx>) -> bool {
        // The representation of an allowed path prefix, e.g. paths
        // with this representation definitely cannot reach a feasible cycle.
        type AllowedPathPrefix<'tcx, 'graph> = Path<'tcx, 'graph>;

        let mut allowed_path_prefixes: FxHashSet<AllowedPathPrefix<'tcx, 'graph>> =
            FxHashSet::default();

        enum PushResult<'tcx, 'graph> {
            ExtendPath(Path<'tcx, 'graph>),
            Cycle,
            PathConditionsUnsatisfiable,
        }

        #[derive(Clone, Debug, Eq, PartialEq, Hash)]
        struct Path<'tcx, 'graph>(Vec<BorrowPCGEdgeRef<'tcx, 'graph>>);
        impl<'tcx, 'graph> Path<'tcx, 'graph> {
            /// Checks if the path is actually feasible, i.e. there is an
            /// execution path of the program such that the path conditions of
            /// each edge are satisfied.
            ///
            /// Note that this check is very conservative right now (basically
            /// only checking some obvious cases)
            fn is_feasible(&self, repacker: PlaceRepacker<'_, 'tcx>) -> bool {
                let leaf_blocks = repacker
                    .body()
                    .basic_blocks
                    .iter_enumerated()
                    .filter(|(_, bb)| matches!(bb.terminator().edges(), TerminatorEdges::None))
                    .map(|(idx, _)| idx)
                    .collect::<Vec<_>>();

                // Maps leaf blocks `be` to a block `bs`, where the path feasibility
                // requires an edge `bs` -> `be`. If `bs` is not unique for some
                // `be`, then the path is definitely not feasible.
                let mut end_blocks_map = FxHashMap::default();
                for edge in self.0.iter() {
                    match edge.conditions() {
                        PathConditions::Paths(pcgraph) => {
                            for block in leaf_blocks.iter() {
                                let edges = pcgraph.edges_to(*block);
                                if edges.len() == 1 {
                                    let from_block = edges.iter().next().unwrap().from;
                                    if let Some(bs) = end_blocks_map.insert(block, from_block) {
                                        if bs != from_block {
                                            return false;
                                        }
                                    }
                                }
                            }
                        }
                        PathConditions::AtBlock(_) => {}
                    }
                }
                true
            }

            fn try_push(
                mut self,
                edge: BorrowPCGEdgeRef<'tcx, 'graph>,
                repacker: PlaceRepacker<'_, 'tcx>,
            ) -> PushResult<'tcx, 'graph> {
                if self.0.iter().any(|e| *e == edge) {
                    PushResult::Cycle
                } else {
                    self.0.push(edge);
                    if self.is_feasible(repacker) {
                        PushResult::ExtendPath(self)
                    } else {
                        PushResult::PathConditionsUnsatisfiable
                    }
                }
            }

            fn last(&self) -> BorrowPCGEdgeRef<'tcx, 'graph> {
                *self.0.last().unwrap()
            }

            fn new(edge: BorrowPCGEdgeRef<'tcx, 'graph>) -> Self {
                Self(vec![edge])
            }

            fn path_prefix_repr(&self) -> AllowedPathPrefix<'tcx, 'graph> {
                self.clone()
            }

            fn leads_to_feasible_cycle<'mir: 'graph>(
                &self,
                graph: &FrozenGraphRef<'graph, 'tcx>,
                repacker: PlaceRepacker<'mir, 'tcx>,
                prefixes: &mut FxHashSet<AllowedPathPrefix<'tcx, 'graph>>,
            ) -> bool {
                let path_prefix_repr = self.path_prefix_repr();
                if prefixes.contains(&path_prefix_repr) {
                    return false;
                }
                let curr = self.last();
                let blocking_edges = curr
                    .blocked_by_nodes(repacker)
                    .into_iter()
                    .flat_map(|node| graph.get_edges_blocking(node.into(), repacker))
                    .unique();
                for edge in blocking_edges {
                    match self.clone().try_push(edge, repacker) {
                        PushResult::Cycle => {
                            return true;
                        }
                        PushResult::ExtendPath(next_path) => {
                            next_path.leads_to_feasible_cycle(graph, repacker, prefixes);
                        }
                        PushResult::PathConditionsUnsatisfiable => {}
                    }
                }
                prefixes.insert(path_prefix_repr);
                false
            }
        }

        for root in self.roots(repacker).iter() {
            for edge in self.get_edges_blocking(*root, repacker) {
                if Path::new(edge).leads_to_feasible_cycle(
                    self,
                    repacker,
                    &mut allowed_path_prefixes,
                ) {
                    return false;
                }
            }
        }

        true
    }

    pub(crate) fn coupled_lifetime_roots<'mir: 'graph>(
        &mut self,
        start_from: FxHashSet<LocalRegionProjection<'tcx>>,
        borrow_checker: &dyn BorrowCheckerInterface<'mir, 'tcx>,
        repacker: PlaceRepacker<'mir, 'tcx>,
    ) -> CoupledRoots<'tcx> {
        debug_assert!(start_from.len() > 1);
        let region = start_from.iter().next().unwrap().region(repacker);
        let mut stack = start_from
            .into_iter()
            .map(|rp| rp.to_local_node(repacker))
            .collect::<Vec<_>>();
        let mut result = CoupledRoots::default();
        while let Some(node) = stack.pop() {
            for edge in self.get_edges_blocked_by(node, repacker).iter() {
                match edge.kind() {
                    BorrowPCGEdgeKind::Borrow(_) => {}
                    BorrowPCGEdgeKind::BorrowPCGExpansion(borrow_pcgexpansion) => {
                        stack.push(borrow_pcgexpansion.base());
                    }
                    BorrowPCGEdgeKind::Abstraction(_) => {}
                    BorrowPCGEdgeKind::Outlives(outlives_edge) => match outlives_edge.kind {
                        OutlivesEdgeKind::Aggregate { .. }
                        | OutlivesEdgeKind::InitialBorrows
                        | OutlivesEdgeKind::HavocRegion
                        | OutlivesEdgeKind::Move
                        | OutlivesEdgeKind::ConstRef => {
                            if borrow_checker
                                .same_region(outlives_edge.short().region(repacker), region)
                            {
                                result.insert(outlives_edge.short(), outlives_edge.long());
                            }
                        }
                        OutlivesEdgeKind::BorrowOutlives { .. } => {
                            stack.push(outlives_edge.long().try_to_local_node(repacker).unwrap());
                        }
                        OutlivesEdgeKind::CopySharedRef => {}
                    },
                    BorrowPCGEdgeKind::RegionProjectionMember(..) => todo!(),
                    BorrowPCGEdgeKind::FunctionCallRegionCoupling(..) => todo!(),
                }
            }
        }
        result
    }
}

#[derive(Default, Debug, Clone, Eq, PartialEq)]
pub(crate) struct CoupledRoots<'tcx>(
    FxHashMap<LocalRegionProjection<'tcx>, FxHashSet<RegionProjection<'tcx>>>,
);

impl<'tcx> CoupledRoots<'tcx> {
    pub(crate) fn insert(
        &mut self,
        node: LocalRegionProjection<'tcx>,
        parent: RegionProjection<'tcx>,
    ) {
        self.0.entry(node).or_default().insert(parent);
    }

    fn all_parents(&self) -> FxHashSet<RegionProjection<'tcx>> {
        self.0.values().flatten().cloned().collect()
    }

    pub fn connections_to_create(
        self,
    ) -> FxHashMap<LocalRegionProjection<'tcx>, FxHashSet<RegionProjection<'tcx>>> {
        let all_parents = self.all_parents();
        self.0
            .into_iter()
            .map(|(node, parents)| (node, all_parents.difference(&parents).cloned().collect()))
            .collect()
    }
}
