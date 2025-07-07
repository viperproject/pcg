use itertools::Itertools;

use crate::{
    borrow_pcg::{
        abstraction::node::AbstractionGraphNode,
        abstraction_graph_constructor::AbstractionGraph,
        borrow_pcg_edge::{BorrowPcgEdgeLike, BorrowPcgEdgeRef, LocalNode},
        edge::kind::BorrowPcgEdgeKind,
        edge_data::EdgeData,
        graph::BorrowsGraph,
        has_pcs_elem::LabelRegionProjection,
        region_projection::{LocalRegionProjection, RegionProjectionLabel},
    },
    coupling::coupled::Coupled,
    pcg::{LocalNodeLike, PCGNode, PCGNodeLike},
    rustc_interface::{
        data_structures::fx::{FxHashMap, FxHashSet},
        middle::mir::{self},
    },
    utils::{
        data_structures::HashSet, liveness::PlaceLiveness, CompilerCtxt, HasPlace, SnapshotLocation,
    },
};

impl<'tcx> BorrowsGraph<'tcx> {
    pub(crate) fn get_loop_abstraction_graph<'mir>(
        &self,
        live_loop_nodes: HashSet<LocalNode<'tcx>>,
        live_roots: HashSet<PCGNode<'tcx>>,
        loop_head: mir::BasicBlock,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> (AbstractionGraph<'tcx>, HashSet<LocalRegionProjection<'tcx>>) {
        let mut graph = AbstractionGraph::new();
        let mut all_nodes = HashSet::default();
        all_nodes.extend(live_loop_nodes.iter().map(|node| node.to_pcg_node(ctxt)));
        all_nodes.extend(live_roots.iter().copied());
        let all_related_places = all_nodes
            .iter()
            .flat_map(|node| node.related_current_place())
            .unique()
            .sorted_by_key(|p| p.projection.len())
            .rev()
            .collect::<Vec<_>>();
        let loop_lifetime_projections: Vec<LocalRegionProjection<'tcx>> = live_loop_nodes
            .iter()
            .flat_map(|node| (*node).try_into())
            .collect::<Vec<_>>();
        let loop_head_location = mir::Location {
            block: loop_head,
            statement_index: 0,
        };
        for borrow in ctxt.bc.borrow_set().location_map().values() {
            let longest_prefix_place = all_related_places
                .iter()
                .find(|p| p.is_prefix(borrow.borrowed_place().into()))
                .copied();
            if let Some(related_place) = longest_prefix_place {
                // N_b
                let blocked_nodes = all_nodes
                    .iter()
                    .filter(|node| {
                        node.related_current_place()
                            .map_or(false, |p| p == related_place)
                    })
                    .copied();

                for blocked_node in blocked_nodes {
                    // RP_b
                    let candidate_blockers = loop_lifetime_projections
                        .iter()
                        .filter(|rp| {
                            blocked_node
                                .related_local()
                                .map_or(true, |local| local != rp.related_local())
                                && ctxt.bc.blocks(
                                    **rp,
                                    borrow.borrowed_place().into(),
                                    loop_head_location,
                                    ctxt,
                                )
                        })
                        .copied()
                        .collect::<Vec<_>>();

                    for blocker in candidate_blockers {
                        graph.add_edge(
                            &Coupled::singleton(blocked_node.try_into().unwrap()),
                            &Coupled::singleton(blocker.to_local_node(ctxt).into()),
                            Default::default(),
                            ctxt,
                        );
                    }
                }
            }
        }
        let loop_head_label = RegionProjectionLabel::Location(SnapshotLocation::Start(loop_head));
        let mut to_label = HashSet::default();
        graph.mut_non_leaf_nodes(|node| {
            node.nodes.mutate(|n| match &mut **n {
                PCGNode::Place(_) => {}
                PCGNode::RegionProjection(region_projection) => {
                    let local_rp: LocalRegionProjection<'tcx> =
                        region_projection.with_base(region_projection.base().try_into().unwrap());
                    if live_roots.contains(&local_rp.into()) {
                        return;
                    }
                    to_label.insert(local_rp);
                    *region_projection = region_projection.with_label(Some(loop_head_label), ctxt);
                }
            });
        });
        (graph, to_label)
    }

    pub(crate) fn get_immediate_live_ancestors<'mir>(
        &self,
        node: LocalNode<'tcx>,
        liveness: &PlaceLiveness<'mir, 'tcx>,
        location: mir::Location,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> HashSet<PCGNode<'tcx>> {
        let mut result = HashSet::default();
        let mut queue = vec![node];
        let mut seen = HashSet::default();
        while let Some(node) = queue.pop() {
            if seen.contains(&node) {
                continue;
            }
            seen.insert(node);
            for edge in self.edges_blocked_by(node, ctxt) {
                if let BorrowPcgEdgeKind::BorrowPcgExpansion(borrow_edge) = edge.kind() {
                    if borrow_edge.is_owned_expansion(ctxt) {
                        result.insert(borrow_edge.deref_blocked_region_projection(ctxt).unwrap());
                        continue;
                    }
                }
                for blocked_by in edge.blocked_nodes(ctxt) {
                    match blocked_by.try_to_local_node(ctxt) {
                        Some(local_node) => {
                            if liveness.is_live(local_node.place(), location) {
                                result.insert(local_node.into());
                            } else {
                                queue.push(local_node);
                            }
                        }
                        None => {
                            result.insert(blocked_by);
                        }
                    }
                }
            }
        }
        result
    }

    pub(crate) fn identify_edges_to_cut<'mir: 'graph, 'graph>(
        &'graph self,
        abstraction_graph_nodes: HashSet<PCGNode<'tcx>>,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> HashSet<BorrowPcgEdgeKind<'tcx>> {
        let mut to_cut = HashSet::default();
        let mut paths: Vec<Vec<&'graph BorrowPcgEdgeKind<'tcx>>> = abstraction_graph_nodes
            .iter()
            .flat_map(|node| {
                self.edges_blocking(*node, ctxt)
                    .map(|edge| vec![edge.kind])
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let mut seen = HashSet::default();
        while let Some(path) = paths.pop() {
            let last_edge = *path.last().unwrap();
            if seen.contains(&last_edge) {
                continue;
            }
            seen.insert(last_edge);
            let blocked_by_nodes = last_edge.blocked_by_nodes(ctxt).collect::<Vec<_>>();
            if blocked_by_nodes
                .iter()
                .any(|node| abstraction_graph_nodes.contains(&node.to_pcg_node(ctxt)))
            {
                to_cut.extend(path);
                continue;
            }
            for blocked_by_node in blocked_by_nodes {
                for edge in self.edges_blocking(blocked_by_node.into(), ctxt) {
                    let mut next_path = path.clone();
                    next_path.push(edge.kind);
                    paths.push(next_path);
                }
            }
        }
        to_cut.into_iter().map(|edge| edge.clone()).collect()
    }
}
