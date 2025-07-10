use itertools::Itertools;

use crate::{
    action::PcgAction, borrow_checker::BorrowLike, borrow_pcg::{
        action::BorrowPcgActionKind,
        borrow_pcg_edge::{BorrowPcgEdgeLike, BorrowPcgEdgeRef, LocalNode, ToBorrowsEdge},
        edge::{
            abstraction::{r#loop::LoopAbstraction, AbstractionBlockEdge},
            kind::BorrowPcgEdgeKind,
        },
        edge_data::EdgeData,
        graph::BorrowsGraph,
        has_pcs_elem::LabelRegionProjectionPredicate,
        path_condition::PathConditions,
        region_projection::{
            LocalRegionProjection, RegionProjectionBaseLike, RegionProjectionLabel,
        },
    }, free_pcs::{CapabilityKind, FreePlaceCapabilitySummary, RepackOp}, pcg::{
        obtain::{Expander, ObtainType},
        place_capabilities::PlaceCapabilities,
        LocalNodeLike, PCGNode, PCGNodeLike,
    }, pcg_validity_assert, rustc_interface::middle::mir::{self}, utils::{
        data_structures::HashSet, display::DisplayWithCompilerCtxt, liveness::PlaceLiveness,
        maybe_old::MaybeOldPlace, maybe_remote::MaybeRemotePlace, CompilerCtxt, HasPlace, Place,
        SnapshotLocation,
    }
};

pub(crate) struct ConstructAbstractionGraphResult<'tcx> {
    pub(crate) graph: BorrowsGraph<'tcx>,
    pub(crate) to_label: HashSet<LabelRegionProjectionPredicate<'tcx>>,
    pub(crate) to_remove: HashSet<Place<'tcx>>,
}

impl<'tcx> ConstructAbstractionGraphResult<'tcx> {
    pub(crate) fn new(
        graph: BorrowsGraph<'tcx>,
        to_label: HashSet<LabelRegionProjectionPredicate<'tcx>>,
        to_remove: HashSet<Place<'tcx>>,
    ) -> Self {
        Self {
            graph,
            to_label,
            to_remove,
        }
    }
}

impl<'tcx> BorrowsGraph<'tcx> {
    pub(crate) fn get_loop_abstraction_graph<'mir>(
        &self,
        live_loop_nodes: HashSet<LocalNode<'tcx>>,
        live_roots: HashSet<PCGNode<'tcx>>,
        loop_head: mir::BasicBlock,
        path_conditions: PathConditions,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> ConstructAbstractionGraphResult<'tcx> {
        let mut graph = BorrowsGraph::default();
        let mut all_nodes = HashSet::default();
        let mut to_remove = HashSet::default();
        let mut to_label = HashSet::default();
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
        tracing::debug!(
            "loop_lifetime_projections: {}",
            all_blocker_candidates.to_short_string(ctxt)
        );
        let loop_head_location = mir::Location {
            block: loop_head,
            statement_index: 0,
        };

        let mut expander = AbsExpander {
            loop_head_block: loop_head,
            graph: &mut graph,
            capabilities: None,
            path_conditions: path_conditions.clone(),
            ctxt,
            owned: None,
        };

        let mut handle_blocked_node =
            |blocked_node: PCGNode<'tcx>,
             predicate: &dyn Fn(LocalRegionProjection<'tcx>) -> bool| {
                let blockers = add_edges_for_blocked_node(
                    &mut expander,
                    blocked_node,
                    &all_blocker_candidates,
                    predicate,
                );
                if !blockers.is_empty() {
                    if let Some(place) = blocked_node.related_current_place() {
                        to_remove.insert(place);
                        for rp in place.region_projections(ctxt) {
                            to_label.insert(LabelRegionProjectionPredicate::AllNonPlaceHolder(
                                place.into(),
                                rp.region_idx,
                            ));
                        }
                    }
                }
                if let Some(PCGNode::RegionProjection(rp)) = blocked_node.try_to_local_node(ctxt) {
                    let nested_rps = blockers
                        .iter()
                        .flat_map(|rp| rp.nested_projections(ctxt))
                        .unique()
                        .collect::<Vec<_>>();
                    for nested_rp in nested_rps.iter() {
                        tracing::debug!("nested_rp: {}", nested_rp.to_short_string(ctxt));
                        add_block_edge(&mut expander, blocked_node, *nested_rp, ctxt);
                    }
                    if !nested_rps.is_empty() {
                        expander
                            .add_and_update_placeholder_edges(
                                rp,
                                &nested_rps
                                    .iter()
                                    .map(|rp| rp.to_region_projection())
                                    .collect::<Vec<_>>(),
                                "add_edges_for_blocked_node",
                                ctxt,
                            )
                            .unwrap();
                    }
                }
            };

        for borrow in ctxt.bc.location_map().values() {
            let borrowed_place: Place<'tcx> = borrow.get_borrowed_place();
            let longest_prefix_of_blocked_place = all_related_places
                .iter()
                .find(|p| p.is_prefix(borrowed_place))
                .copied();
            if let Some(related_place) = longest_prefix_of_blocked_place {
                tracing::debug!(
                    "{} is related to blocked place {}",
                    related_place.to_short_string(ctxt),
                    borrowed_place.to_short_string(ctxt)
                );
                // N_b
                let blocked_nodes = all_nodes
                    .iter()
                    .filter(|node| node.related_current_place() == Some(related_place))
                    .copied();

                for blocked_node in blocked_nodes {
                    handle_blocked_node(blocked_node, &|rp| {
                        rp.related_local() != blocked_node.related_local().unwrap()
                            && ctxt.bc.blocks(
                                rp,
                                blocked_node.related_current_place().unwrap(),
                                loop_head_location,
                                ctxt,
                            )
                    });
                }
            } else {
                tracing::debug!(
                    "no related place found for borrow of {}",
                    borrowed_place.to_short_string(ctxt)
                );
            }
        }
        for root in live_roots.iter() {
            match root {
                PCGNode::RegionProjection(rp) if rp.is_remote(ctxt) => {
                    handle_blocked_node(*root, &|candidate_blocker| {
                        ctxt.bc
                            .outlives(rp.region(ctxt), candidate_blocker.region(ctxt))
                    });
                }
                PCGNode::Place(MaybeRemotePlace::Remote(place)) => {
                    handle_blocked_node(*root, &|candidate_blocker| {
                        place
                            .regions(ctxt)
                            .into_iter()
                            .any(|region| ctxt.bc.outlives(region, candidate_blocker.region(ctxt)))
                    });
                }
                _ => {}
            }
        }
        expander
            .graph
            .render_debug_graph(ctxt, "Abstraction graph before expansion");
        for place in all_related_places {
            tracing::debug!("expanding to {}", place.to_short_string(ctxt));
            expander
                .expand_to(
                    place,
                    ObtainType::Capability(CapabilityKind::Exclusive),
                    ctxt,
                )
                .unwrap();
        }
        expander
            .graph
            .render_debug_graph(ctxt, "Abstraction graph after expansion");
        let loop_head_label = RegionProjectionLabel::Location(SnapshotLocation::Loop(loop_head));
        let frozen_graph = graph.frozen_graph();
        tracing::debug!(
            "leaf edges: {}",
            frozen_graph.leaf_edges(ctxt).to_short_string(ctxt)
        );
        tracing::debug!(
            "leaf nodes: {}",
            frozen_graph.leaf_nodes(ctxt).to_short_string(ctxt)
        );
        for rp in to_label.iter() {
            tracing::debug!("labeling {:?}", rp);
            graph.label_region_projection(rp, Some(loop_head_label), ctxt);
        }
        ConstructAbstractionGraphResult::new(graph, to_label, to_remove)
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
            let mut blocked_edges = self.edges_blocked_by(node, ctxt).peekable();
            if blocked_edges.peek().is_none() {
                result.insert(node.to_pcg_node(ctxt));
                continue;
            }
            for edge in blocked_edges {
                if let BorrowPcgEdgeKind::BorrowPcgExpansion(borrow_edge) = edge.kind() {
                    if borrow_edge.is_owned_expansion(ctxt) {
                        let deref_blocked_region_projection = borrow_edge
                            .deref_blocked_region_projection(ctxt)
                            .unwrap_or_else(|| {
                                panic!(
                                    "No deref blocked region projection for {}: {:?}",
                                    borrow_edge.base.to_short_string(ctxt),
                                    borrow_edge.base.related_current_place().unwrap().ty(ctxt)
                                );
                            });
                        queue.push(
                            deref_blocked_region_projection
                                .try_to_local_node(ctxt)
                                .unwrap(),
                        );
                    } else {
                        queue.push(borrow_edge.base);
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
        tracing::debug!(
            "immediate live ancestors of {}: {}",
            node.to_short_string(ctxt),
            result.to_short_string(ctxt)
        );
        result
    }

    pub(crate) fn unpack_places_for_abstraction<'mir>(
        &mut self,
        loop_head_block: mir::BasicBlock,
        live_loop_places: &HashSet<Place<'tcx>>,
        capabilities: &mut PlaceCapabilities<'tcx>,
        owned: &mut FreePlaceCapabilitySummary<'tcx>,
        path_conditions: PathConditions,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) {
        let mut expander = AbsExpander {
            loop_head_block,
            graph: self,
            capabilities: Some(capabilities),
            owned: Some(owned),
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
        'outer: while let Some(path) = paths.pop() {
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
                    if path.contains(&edge) {
                        pcg_validity_assert!(false, "edge already in path");
                        // For debugging, just stop here and we can try to visualize the graph
                        break 'outer;
                    }
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
    owned: Option<&'pcg mut FreePlaceCapabilitySummary<'tcx>>,
    path_conditions: PathConditions,
    ctxt: CompilerCtxt<'mir, 'tcx>,
}

impl<'mir, 'tcx> Expander<'mir, 'tcx> for AbsExpander<'_, 'mir, 'tcx> {
    fn apply_action(&mut self, action: PcgAction<'tcx>) -> Result<bool, crate::pcg::PcgError> {
        tracing::debug!("applying action: {}", action.debug_line(self.ctxt));
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
                BorrowPcgActionKind::RedirectEdge { .. } => todo!(),
                BorrowPcgActionKind::LabelRegionProjection(
                    region_projection,
                    region_projection_label,
                ) => Ok(self.graph.label_region_projection(
                    &LabelRegionProjectionPredicate::Equals(region_projection),
                    region_projection_label,
                    self.ctxt,
                )),
                BorrowPcgActionKind::Weaken(_) => todo!(),
                BorrowPcgActionKind::Restore(_) => todo!(),
                BorrowPcgActionKind::MakePlaceOld(_, _) => todo!(),
                BorrowPcgActionKind::SetLatest(_, _) => todo!(),
                BorrowPcgActionKind::RemoveEdge(borrow_pcg_edge) => {
                    self.graph.remove(borrow_pcg_edge.kind());
                    Ok(true)
                }
            },
            PcgAction::Owned(action) => match action.kind {
                RepackOp::StorageDead(_) => todo!(),
                RepackOp::IgnoreStorageDead(_) => todo!(),
                RepackOp::Weaken(_, _, _) => todo!(),
                RepackOp::Expand(repack_expand) => {
                    if let Some(owned) = &mut self.owned {
                        owned.perform_expand_action(
                            repack_expand,
                            self.capabilities.as_mut().unwrap(),
                            self.ctxt,
                        )?;
                    } else {
                        unreachable!()
                    }
                    Ok(true)
                }
                RepackOp::Collapse(_) => todo!(),
                RepackOp::DerefShallowInit(_, _) => todo!(),
                RepackOp::RegainLoanedCapability(_, _) => todo!(),
            },
        }
    }

    fn current_snapshot_location(&self) -> SnapshotLocation {
        SnapshotLocation::Loop(self.loop_head_block)
    }

    fn borrows_graph(&self) -> &BorrowsGraph<'tcx> {
        self.graph
    }

    fn path_conditions(&self) -> PathConditions {
        self.path_conditions.clone()
    }

    fn contains_owned_expansion_from(&self, base: Place<'tcx>) -> bool {
        if let Some(owned) = &self.owned {
            owned.locals()[base.local]
                .get_allocated()
                .contains_expansion_from(base)
        } else {
            // Pretend we're always fully expanded in the local PCG
            true
        }
    }
}

fn add_block_edge<'tcx>(
    expander: &mut AbsExpander<'_, '_, 'tcx>,
    blocked_node: PCGNode<'tcx>,
    blocker: LocalRegionProjection<'tcx>,
    ctxt: CompilerCtxt<'_, 'tcx>,
) {
    let abstraction_block_edge = AbstractionBlockEdge::new(
        vec![blocked_node.to_pcg_node(ctxt).into()],
        vec![blocker.to_local_node(ctxt).into()],
        ctxt,
    );
    let loop_edge = LoopAbstraction::new(abstraction_block_edge, expander.loop_head_block);
    expander.graph.insert(
        loop_edge.to_borrow_pcg_edge(expander.path_conditions.clone()),
        ctxt,
    );
}

fn add_edges_for_blocked_node<'tcx>(
    expander: &mut AbsExpander<'_, '_, 'tcx>,
    blocked_node: PCGNode<'tcx>,
    all_blocker_candidates: &[LocalRegionProjection<'tcx>],
    check_blocks: impl Fn(LocalRegionProjection<'tcx>) -> bool,
) -> Vec<LocalRegionProjection<'tcx>> {
    let ctxt = expander.ctxt;
    tracing::debug!("blocked_node: {}", blocked_node.to_short_string(ctxt));
    // RP_b
    let candidate_blockers = all_blocker_candidates
        .iter()
        .filter(|rp| check_blocks(**rp))
        .copied()
        .collect::<Vec<_>>();
    tracing::debug!(
        "candidate_blockers: {}",
        candidate_blockers.to_short_string(ctxt)
    );

    for blocker in candidate_blockers.iter() {
        add_block_edge(expander, blocked_node, *blocker, ctxt);
    }
    candidate_blockers
}
