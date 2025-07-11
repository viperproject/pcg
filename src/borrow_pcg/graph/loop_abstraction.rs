use derive_more::From;

use crate::{
    action::PcgAction,
    borrow_checker::{BorrowCheckerInterface, BorrowLike},
    borrow_pcg::{
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
        region_projection::{RegionProjection, RegionProjectionBaseLike, RegionProjectionLabel},
    },
    free_pcs::{CapabilityKind, FreePlaceCapabilitySummary, RepackOp},
    pcg::{
        obtain::{Expander, ObtainType},
        place_capabilities::PlaceCapabilities,
        LocalNodeLike, PCGNode, PCGNodeLike,
    },
    pcg_validity_assert,
    rustc_interface::middle::mir::{self},
    utils::{
        data_structures::HashSet, display::DisplayWithCompilerCtxt, remote::RemotePlace,
        CompilerCtxt, Place, SnapshotLocation,
    },
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, From)]
pub(crate) enum MaybeRemoteCurrentPlace<'tcx> {
    Local(Place<'tcx>),
    Remote(RemotePlace),
}

impl<'tcx, 'a> DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>
    for MaybeRemoteCurrentPlace<'tcx>
{
    fn to_short_string(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    ) -> String {
        match self {
            MaybeRemoteCurrentPlace::Local(place) => place.to_short_string(ctxt),
            MaybeRemoteCurrentPlace::Remote(place) => place.to_short_string(ctxt),
        }
    }
}
impl<'tcx> MaybeRemoteCurrentPlace<'tcx> {
    fn to_pcg_node(self, ctxt: CompilerCtxt<'_, 'tcx>) -> PCGNode<'tcx> {
        match self {
            MaybeRemoteCurrentPlace::Local(place) => place.to_pcg_node(ctxt),
            MaybeRemoteCurrentPlace::Remote(place) => place.to_pcg_node(ctxt),
        }
    }

    pub(crate) fn relevant_place_for_blocking(self) -> Place<'tcx> {
        match self {
            MaybeRemoteCurrentPlace::Local(place) => place,
            MaybeRemoteCurrentPlace::Remote(place) => place.local.into(),
        }
    }

    pub(crate) fn is_local(self) -> bool {
        matches!(self, MaybeRemoteCurrentPlace::Local(_))
    }

    pub(crate) fn is_remote(self) -> bool {
        matches!(self, MaybeRemoteCurrentPlace::Remote(_))
    }

    fn region_projections(self, ctxt: CompilerCtxt<'_, 'tcx>) -> Vec<RegionProjection<'tcx>> {
        match self {
            MaybeRemoteCurrentPlace::Local(place) => place
                .region_projections(ctxt)
                .into_iter()
                .map(|rp| rp.to_pcg_node(ctxt).try_into_region_projection().unwrap())
                .collect(),
            MaybeRemoteCurrentPlace::Remote(place) => place
                .region_projections(ctxt)
                .into_iter()
                .map(|rp| rp.to_pcg_node(ctxt).try_into_region_projection().unwrap())
                .collect(),
        }
    }
}
impl<'tcx> BorrowsGraph<'tcx> {
    pub(crate) fn get_loop_abstraction_graph<'mir>(
        &self,
        loop_places: HashSet<Place<'tcx>>,
        root_places: HashSet<MaybeRemoteCurrentPlace<'tcx>>,
        blocker_places: HashSet<Place<'tcx>>,
        loop_head: mir::BasicBlock,
        path_conditions: PathConditions,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> ConstructAbstractionGraphResult<'tcx> {
        let mut graph = BorrowsGraph::default();
        // let mut all_nodes = HashSet::default();
        let mut to_remove = HashSet::default();
        let mut to_label = HashSet::default();

        tracing::info!(
            "loop_places at {:?} : {}",
            loop_head,
            loop_places.to_short_string(ctxt)
        );

        let candidate_blockers = loop_places
            .iter()
            .filter(|place| !place.regions(ctxt).is_empty())
            .copied()
            .collect::<Vec<_>>();

        tracing::info!(
            "candidate_blockers at {:?} : {}",
            loop_head,
            candidate_blockers.to_short_string(ctxt)
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

        for blocker in blocker_places.into_iter() {
            // let ancestor_nodes = self.get_borrow_roots(blocker.into(), ctxt);
            // tracing::info!(
            //     "immediate live ancestors of {}: {}",
            //     blocker.to_short_string(ctxt),
            //     ancestor_nodes.to_short_string(ctxt)
            // );
            // let root_places = ancestor_nodes
            //     .into_iter()
            //     .flat_map(|root| root.related_maybe_remote_current_place())
            //     .filter(|p| match p {
            //         MaybeRemoteCurrentPlace::Local(place) => !loop_places.contains(place),
            //         MaybeRemoteCurrentPlace::Remote(_) => true,
            //     })
            //     .collect::<HashSet<_>>();
            // tracing::info!(
            //     "immediate live place ancestors of {}: {}",
            //     blocker.to_short_string(ctxt),
            //     root_places.to_short_string(ctxt)
            // );
            for root in root_places.iter() {
                let relevant_root = root.relevant_place_for_blocking();
                if blocker == relevant_root
                    || ctxt
                        .bc
                        .blocks(blocker, relevant_root, loop_head_location, ctxt)
                {
                    tracing::info!(
                        "{} blocks root {}",
                        blocker.to_short_string(ctxt),
                        relevant_root.to_short_string(ctxt)
                    );
                    add_block_edges(&mut expander, *root, blocker, ctxt);
                    if let MaybeRemoteCurrentPlace::Local(root) = root {
                        for rp in root.region_projections(ctxt) {
                            to_label.insert(LabelRegionProjectionPredicate::AllNonPlaceHolder(
                                (*root).into(),
                                rp.region_idx,
                            ));
                        }
                    }
                } else if root.is_remote() {
                    add_rp_block_edges(&mut expander, *root, blocker, ctxt);
                }
            }
        }

        for borrow in ctxt.bc.location_map().values() {
            let blocked_place: Place<'tcx> = borrow.get_borrowed_place();
            let blockers = add_edges_for_blocked_place(
                &mut expander,
                blocked_place.into(),
                &candidate_blockers,
                |candidate_blocker| {
                    ctxt.bc
                        .blocks(candidate_blocker, blocked_place, loop_head_location, ctxt)
                },
            );

            if !blockers.is_empty() {
                to_remove.insert(blocked_place);
                for rp in blocked_place.region_projections(ctxt) {
                    to_label.insert(LabelRegionProjectionPredicate::AllNonPlaceHolder(
                        blocked_place.into(),
                        rp.region_idx,
                    ));
                }
            }
        }
        expander
            .graph
            .render_debug_graph(ctxt, "Abstraction graph before expansion");
        for place in loop_places {
            tracing::info!("expanding to {}", place.to_short_string(ctxt));
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
        tracing::info!(
            "leaf edges: {}",
            frozen_graph.leaf_edges(ctxt).to_short_string(ctxt)
        );
        tracing::info!(
            "leaf nodes: {}",
            frozen_graph.leaf_nodes(ctxt).to_short_string(ctxt)
        );
        for rp in to_label.iter() {
            tracing::debug!("labeling {:?}", rp);
            graph.label_region_projection(rp, Some(loop_head_label), ctxt);
        }
        ConstructAbstractionGraphResult::new(graph, to_label, to_remove)
    }

    pub(crate) fn get_borrow_roots(
        &self,
        node: Place<'tcx>,
        loop_head_block: mir::BasicBlock,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> HashSet<PCGNode<'tcx>> {
        let mut result = HashSet::default();
        let mut queue: Vec<LocalNode<'tcx>> = node
            .region_projections(ctxt)
            .into_iter()
            .flat_map(|rp| {
                vec![
                    rp.to_local_node(ctxt),
                    rp.with_label(
                        Some(RegionProjectionLabel::Location(SnapshotLocation::Loop(
                            loop_head_block,
                        ))),
                        ctxt,
                    )
                    .to_local_node(ctxt),
                ]
            })
            .collect();
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
                        queue.push(deref_blocked_region_projection.into());
                    } else {
                        queue.push(borrow_edge.base);
                    }
                    continue;
                }
                for blocked_by in edge.blocked_nodes(ctxt) {
                    match blocked_by.try_to_local_node(ctxt) {
                        Some(local_node) => {
                            if local_node.related_current_place().is_some() {
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
        blocked_loop_places: &HashSet<Place<'tcx>>,
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
        let mut to_expand: Vec<Place<'tcx>> = vec![];
        for place in blocked_loop_places {
            if to_expand.iter().any(|p| place.is_prefix(*p)) {
                continue;
            }
            to_expand.retain(|p| !p.is_prefix(*place));
            to_expand.push(*place);
        }
        tracing::info!("to_expand: {}", to_expand.to_short_string(ctxt));
        for place in to_expand {
            expander
                .expand_to(
                    place,
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
        tracing::info!("applying action: {}", action.debug_line(self.ctxt));
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

fn add_block_edge<'tcx, 'mir>(
    expander: &mut AbsExpander<'_, 'mir, 'tcx>,
    long: PCGNode<'tcx>,
    short: LocalNode<'tcx>,
    ctxt: CompilerCtxt<'mir, 'tcx>,
) {
    let long_edge = AbstractionBlockEdge::new(vec![long.into()], vec![short.into()], ctxt);
    let loop_edge = LoopAbstraction::new(long_edge, expander.loop_head_block);
    expander.graph.insert(
        loop_edge.to_borrow_pcg_edge(expander.path_conditions.clone()),
        ctxt,
    );
}

fn add_rp_block_edges<'mir, 'tcx>(
    expander: &mut AbsExpander<'_, 'mir, 'tcx>,
    blocked_place: MaybeRemoteCurrentPlace<'tcx>,
    blocker: Place<'tcx>,
    ctxt: CompilerCtxt<'mir, 'tcx>,
) {
    let blocker_rps = blocker.region_projections(ctxt);
    for blocked_rp in blocked_place.region_projections(ctxt) {
        let flow_rps = blocker_rps
            .iter()
            .filter(|blocker_rp| {
                ctxt.bc
                    .outlives(blocked_rp.region(ctxt), blocker_rp.region(ctxt))
            })
            .copied()
            .collect::<Vec<_>>();
        if let Some(blocked_node) = blocked_rp.try_to_local_node(ctxt) {
            let blocked_rp = blocked_node.try_into_region_projection().unwrap();
            let mut_rps = flow_rps
                .iter()
                .filter_map(|rp| {
                    if rp.is_invariant_in_type(ctxt)
                        && ctxt.bc.outlives(rp.region(ctxt), blocked_rp.region(ctxt))
                    {
                        Some(rp.rebase())
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>();
            if !mut_rps.is_empty() {
                tracing::info!(
                    "Mutable rps: {} -> {}",
                    blocked_rp.to_short_string(ctxt),
                    mut_rps.to_short_string(ctxt)
                );
                expander
                    .add_and_update_placeholder_edges(blocked_rp, &mut_rps, "mut rps", ctxt)
                    .unwrap();
                expander
                    .graph
                    .render_debug_graph(ctxt, "Abstraction graph after adding mut rps");
            }
        }
        for flow_rp in flow_rps {
            add_block_edge(
                expander,
                blocked_rp.into(),
                flow_rp.to_local_node(ctxt),
                ctxt,
            );
        }
    }
}

fn add_block_edges<'mir, 'tcx>(
    expander: &mut AbsExpander<'_, 'mir, 'tcx>,
    blocked_place: MaybeRemoteCurrentPlace<'tcx>,
    blocker: Place<'tcx>,
    ctxt: CompilerCtxt<'mir, 'tcx>,
) {
    assert_ne!(MaybeRemoteCurrentPlace::Local(blocker), blocked_place);
    let blocker_rps = blocker.region_projections(ctxt);
    // Add top-level borrow
    add_block_edge(
        expander,
        blocked_place.to_pcg_node(ctxt),
        blocker_rps[0.into()].to_local_node(ctxt),
        ctxt,
    );
    add_rp_block_edges(expander, blocked_place, blocker, ctxt);
}

fn add_edges_for_blocked_place<'tcx>(
    expander: &mut AbsExpander<'_, '_, 'tcx>,
    blocked_place: MaybeRemoteCurrentPlace<'tcx>,
    all_blocker_candidates: &[Place<'tcx>],
    check_blocks: impl Fn(Place<'tcx>) -> bool,
) -> Vec<Place<'tcx>> {
    let ctxt = expander.ctxt;

    let candidate_blockers = all_blocker_candidates
        .iter()
        .filter(|rp| check_blocks(**rp))
        .copied()
        .collect::<Vec<_>>();
    tracing::info!(
        "candidate_blockers of {}: {}",
        blocked_place.to_short_string(ctxt),
        candidate_blockers.to_short_string(ctxt)
    );

    for blocker in candidate_blockers.iter() {
        add_block_edges(expander, blocked_place, *blocker, ctxt);
    }
    candidate_blockers
}
