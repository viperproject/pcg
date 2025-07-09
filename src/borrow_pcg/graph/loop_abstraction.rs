use itertools::Itertools;

use crate::{
    action::{BorrowPcgAction, PcgAction},
    borrow_pcg::{
        abstraction::node::AbstractionGraphNode,
        abstraction_graph_constructor::AbstractionGraph,
        action::BorrowPcgActionKind,
        borrow_pcg_edge::{
            BorrowPcgEdge, BorrowPcgEdgeLike, BorrowPcgEdgeRef, LocalNode, ToBorrowsEdge,
        },
        edge::{
            abstraction::{r#loop::LoopAbstraction, AbstractionBlockEdge},
            kind::BorrowPcgEdgeKind,
        },
        edge_data::EdgeData,
        graph::BorrowsGraph,
        has_pcs_elem::{LabelRegionProjection, LabelRegionProjectionPredicate},
        path_condition::PathConditions,
        region_projection::{
            LocalRegionProjection, MaybeRemoteRegionProjectionBase, RegionProjectionBaseLike,
            RegionProjectionLabel,
        },
    },
    coupling::coupled::Coupled,
    free_pcs::CapabilityKind,
    pcg::{
        obtain::{Expander, ObtainType},
        place_capabilities::{PlaceCapabilities, PlaceCapabilitiesInterface},
        LocalNodeLike, PCGNode, PCGNodeLike,
    },
    rustc_interface::{
        data_structures::fx::{FxHashMap, FxHashSet},
        middle::mir::{self},
    },
    utils::{
        data_structures::HashSet, display::DisplayWithCompilerCtxt, liveness::PlaceLiveness,
        maybe_old::MaybeOldPlace, maybe_remote::MaybeRemotePlace, CompilerCtxt, HasPlace, Place,
        SnapshotLocation,
    },
};

impl<'tcx> BorrowsGraph<'tcx> {
    pub(crate) fn get_loop_abstraction_graph<'mir>(
        &self,
        live_loop_nodes: HashSet<LocalNode<'tcx>>,
        live_roots: HashSet<PCGNode<'tcx>>,
        loop_head: mir::BasicBlock,
        path_conditions: PathConditions,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> (
        BorrowsGraph<'tcx>,
        HashSet<LabelRegionProjectionPredicate<'tcx>>,
    ) {
        let mut graph = BorrowsGraph::default();
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
        let all_blocker_candidates: Vec<LocalRegionProjection<'tcx>> = live_loop_nodes
            .iter()
            .flat_map(|node| match node {
                PCGNode::Place(MaybeOldPlace::Current { place }) => {
                    let deref_rp = place.closest_deref_rp(ctxt)?;
                    Some(deref_rp.with_base(deref_rp.base.into()))
                }
                PCGNode::RegionProjection(region_projection) => Some(*region_projection),
                _ => None,
            })
            .unique()
            .collect::<Vec<_>>();
        tracing::info!(
            "loop_lifetime_projections: {}",
            all_blocker_candidates.to_short_string(ctxt)
        );
        let loop_head_location = mir::Location {
            block: loop_head,
            statement_index: 0,
        };

        for borrow in ctxt.bc.borrow_set().location_map().values() {
            let borrowed_place: Place<'tcx> = borrow.borrowed_place().into();
            let longest_prefix_of_blocked_place = all_related_places
                .iter()
                .find(|p| p.is_prefix(borrowed_place))
                .copied();
            if let Some(related_place) = longest_prefix_of_blocked_place {
                tracing::info!(
                    "{} is related to blocked place {}",
                    related_place.to_short_string(ctxt),
                    borrowed_place.to_short_string(ctxt)
                );
                // N_b
                let blocked_nodes = all_nodes
                    .iter()
                    .filter(|node| {
                        node.related_current_place()
                            .map_or(false, |p| p == related_place)
                    })
                    .copied();

                for blocked_node in blocked_nodes {
                    add_edges_for_blocked_node(
                        &mut graph,
                        blocked_node,
                        &all_blocker_candidates,
                        |rp| {
                            rp.related_local() != blocked_node.related_local().unwrap()
                                && ctxt.bc.blocks(
                                    rp,
                                    blocked_node.related_current_place().unwrap(),
                                    loop_head_location,
                                    ctxt,
                                )
                        },
                        loop_head,
                        path_conditions.clone(),
                        ctxt,
                    );
                }
            } else {
                tracing::info!(
                    "no related place found for borrow of {}",
                    borrowed_place.to_short_string(ctxt)
                );
            }
        }
        for root in live_roots.iter() {
            match root {
                PCGNode::RegionProjection(rp) if rp.is_remote(ctxt) => {
                    add_edges_for_blocked_node(
                        &mut graph,
                        *root,
                        &all_blocker_candidates,
                        |candidate_blocker| {
                            ctxt.bc
                                .outlives(rp.region(ctxt), candidate_blocker.region(ctxt))
                        },
                        loop_head,
                        path_conditions.clone(),
                        ctxt,
                    );
                }
                PCGNode::Place(MaybeRemotePlace::Remote(place)) => {
                    add_edges_for_blocked_node(
                        &mut graph,
                        *root,
                        &all_blocker_candidates,
                        |candidate_blocker| {
                            place.regions(ctxt).into_iter().any(|region| {
                                ctxt.bc.outlives(region, candidate_blocker.region(ctxt))
                            })
                        },
                        loop_head,
                        path_conditions.clone(),
                        ctxt,
                    );
                }
                _ => {}
            }
        }
        let mut expander = AbsExpander {
            loop_head_block: loop_head,
            graph: &mut graph,
            capabilities: None,
            path_conditions,
            ctxt,
        };
        for place in all_related_places {
            expander
                .expand_to(
                    place,
                    ObtainType::Capability(CapabilityKind::Exclusive),
                    ctxt,
                )
                .unwrap();
        }
        let loop_head_label = RegionProjectionLabel::Location(SnapshotLocation::Start(loop_head));
        let mut to_label = HashSet::default();
        let frozen_graph = graph.frozen_graph();
        for node in graph.nodes(ctxt) {
            if let PCGNode::RegionProjection(rp) = node {
                if let Some(local_rp) = rp.try_to_local_node(ctxt) {
                    if !frozen_graph.is_leaf(local_rp, ctxt) && !frozen_graph.is_root(node, ctxt) {
                        let local_rp = local_rp.try_into_region_projection().unwrap();
                        to_label.insert(LabelRegionProjectionPredicate::AllNonPlaceHolder(
                            local_rp.place().into(),
                            local_rp.region_idx,
                        ));
                    }
                }
            }
        }
        for rp in to_label.iter() {
            graph.label_region_projection(rp, Some(loop_head_label), ctxt);
        }
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
                        queue.push(
                            borrow_edge
                                .deref_blocked_region_projection(ctxt)
                                .unwrap()
                                .try_to_local_node(ctxt)
                                .unwrap(),
                        );
                    } else {
                        queue.push(borrow_edge.base.into());
                    }
                    continue;
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

    pub(crate) fn unpack_places_for_abstraction<'mir>(
        &mut self,
        loop_head_block: mir::BasicBlock,
        live_loop_places: &HashSet<Place<'tcx>>,
        capabilities: &mut PlaceCapabilities<'tcx>,
        path_conditions: PathConditions,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) {
        let mut expander = AbsExpander {
            loop_head_block,
            graph: self,
            capabilities: Some(capabilities),
            path_conditions,
            ctxt,
        };
        for place in live_loop_places {
            expander
                .expand_to(
                    *place,
                    ObtainType::Capability(CapabilityKind::Exclusive),
                    ctxt,
                )
                .unwrap();
        }
    }

    pub(crate) fn identify_subgraph_to_cut<'mir: 'graph, 'graph>(
        &'graph self,
        abstraction_graph_nodes: HashSet<PCGNode<'tcx>>,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> BorrowsGraph<'tcx> {
        let mut to_cut = HashSet::default();
        let mut paths: Vec<Vec<BorrowPcgEdgeRef<'tcx, 'graph>>> = abstraction_graph_nodes
            .iter()
            .flat_map(|node| self.edges_blocking(*node, ctxt).collect::<Vec<_>>())
            .map(|edge| vec![edge])
            .collect::<Vec<_>>();
        while let Some(path) = paths.pop() {
            let last_edge = *path.last().unwrap();
            if to_cut.contains(&last_edge) {
                to_cut.extend(path);
                continue;
            }
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
                    next_path.push(edge);
                    paths.push(next_path);
                }
            }
        }
        let mut graph = BorrowsGraph::default();
        for edge in to_cut {
            graph.insert(edge.to_owned_edge(), ctxt);
        }
        graph
    }
}

struct AbsExpander<'pcg, 'mir, 'tcx> {
    loop_head_block: mir::BasicBlock,
    graph: &'pcg mut BorrowsGraph<'tcx>,
    capabilities: Option<&'pcg mut PlaceCapabilities<'tcx>>,
    path_conditions: PathConditions,
    ctxt: CompilerCtxt<'mir, 'tcx>,
}

impl<'pcg, 'mir, 'tcx> Expander<'mir, 'tcx> for AbsExpander<'pcg, 'mir, 'tcx> {
    fn apply_action(&mut self, action: PcgAction<'tcx>) -> Result<bool, crate::pcg::PcgError> {
        match action {
            PcgAction::Borrow(action) => match action.kind {
                BorrowPcgActionKind::AddEdge { edge, for_read } => {
                    if let Some(capabilities) = &mut self.capabilities {
                        self.graph
                            .handle_add_edge(edge, for_read, capabilities, self.ctxt)
                    } else {
                        self.graph.insert(edge, self.ctxt);
                        Ok(true)
                    }
                }
                BorrowPcgActionKind::RedirectEdge { edge, from, to } => todo!(),
                BorrowPcgActionKind::LabelRegionProjection(
                    region_projection,
                    region_projection_label,
                ) => Ok(self.graph.label_region_projection(
                    &LabelRegionProjectionPredicate::Equals(region_projection),
                    region_projection_label,
                    self.ctxt,
                )),
                BorrowPcgActionKind::Weaken(weaken) => todo!(),
                BorrowPcgActionKind::Restore(restore_capability) => todo!(),
                BorrowPcgActionKind::MakePlaceOld(place, make_place_old_reason) => todo!(),
                BorrowPcgActionKind::SetLatest(place, snapshot_location) => todo!(),
                BorrowPcgActionKind::RemoveEdge(borrow_pcg_edge) => todo!(),
            },
            PcgAction::Owned(action_kind_with_debug_ctxt) => unreachable!(),
        }
    }

    fn expand_owned_place_one_level(
        &mut self,
        base: Place<'tcx>,
        expansion: &crate::utils::ShallowExpansion<'tcx>,
        obtain_type: crate::pcg::obtain::ObtainType,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> Result<bool, crate::pcg::PcgError> {
        todo!()
    }

    fn current_snapshot_location(&self) -> SnapshotLocation {
        SnapshotLocation::Start(self.loop_head_block)
    }

    fn borrows_graph(&self) -> &BorrowsGraph<'tcx> {
        self.graph
    }

    fn path_conditions(&self) -> PathConditions {
        self.path_conditions.clone()
    }
}

fn add_edges_for_blocked_node<'tcx>(
    graph: &mut BorrowsGraph<'tcx>,
    blocked_node: PCGNode<'tcx>,
    all_blocker_candidates: &[LocalRegionProjection<'tcx>],
    check_blocks: impl Fn(LocalRegionProjection<'tcx>) -> bool,
    loop_head: mir::BasicBlock,
    path_conditions: PathConditions,
    ctxt: CompilerCtxt<'_, 'tcx>,
) {
    tracing::info!("blocked_node: {}", blocked_node.to_short_string(ctxt));
    // RP_b
    let candidate_blockers = all_blocker_candidates
        .iter()
        .filter(|rp| check_blocks(**rp))
        .copied()
        .collect::<Vec<_>>();
    tracing::info!(
        "candidate_blockers: {}",
        candidate_blockers.to_short_string(ctxt)
    );

    for blocker in candidate_blockers {
        let abstraction_block_edge = AbstractionBlockEdge::new(
            vec![blocked_node.to_pcg_node(ctxt).into()],
            vec![blocker.to_local_node(ctxt).into()],
            ctxt,
        );
        let loop_edge = LoopAbstraction::new(abstraction_block_edge, loop_head);
        graph.insert(loop_edge.to_borrow_pcg_edge(path_conditions.clone()), ctxt);
    }
}
