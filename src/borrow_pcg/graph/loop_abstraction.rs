use derive_more::From;

use crate::{
    action::PcgAction,
    borrow_checker::BorrowCheckerInterface,
    borrow_pcg::{
        action::BorrowPcgActionKind,
        borrow_pcg_edge::{BorrowPcgEdgeLike, BorrowPcgEdgeRef, LocalNode, ToBorrowsEdge},
        edge::abstraction::{AbstractionBlockEdge, r#loop::LoopAbstraction},
        edge_data::EdgeData,
        graph::{BorrowsGraph, join::JoinBorrowsArgs},
        has_pcs_elem::LabelLifetimeProjectionPredicate,
        path_condition::ValidityConditions,
        region_projection::{
            LifetimeProjection, LifetimeProjectionLabel, RegionIdx, RegionProjectionBaseLike,
        },
        state::BorrowStateMutRef,
    },
    r#loop::{PlaceUsage, PlaceUsageType, PlaceUsages},
    owned_pcg::RepackOp,
    pcg::CapabilityKind,
    pcg::{
        LocalNodeLike, PCGNodeLike, PcgMutRef, PcgNode,
        ctxt::AnalysisCtxt,
        obtain::{
            ActionApplier, HasSnapshotLocation, ObtainType, PlaceExpander, PlaceObtainer,
            RenderDebugGraph,
        },
        place_capabilities::PlaceCapabilities,
    },
    pcg_validity_assert,
    rustc_interface::middle::mir::{self},
    utils::{
        CompilerCtxt, DebugImgcat, Place, SnapshotLocation,
        data_structures::{HashMap, HashSet},
        display::DisplayWithCompilerCtxt,
        logging::{self, LogPredicate},
        maybe_old::MaybeLabelledPlace,
        remote::RemotePlace,
    },
};

pub(crate) struct ConstructAbstractionGraphResult<'tcx> {
    pub(crate) graph: BorrowsGraph<'tcx>,
    pub(crate) to_label: HashSet<LabelLifetimeProjectionPredicate<'tcx>>,
    pub(crate) capability_updates: HashMap<Place<'tcx>, Option<CapabilityKind>>,
}

impl<'tcx> ConstructAbstractionGraphResult<'tcx> {
    pub(crate) fn new(
        graph: BorrowsGraph<'tcx>,
        to_label: HashSet<LabelLifetimeProjectionPredicate<'tcx>>,
        capability_updates: HashMap<Place<'tcx>, Option<CapabilityKind>>,
    ) -> Self {
        Self {
            graph,
            to_label,
            capability_updates,
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
    fn to_pcg_node(self, ctxt: CompilerCtxt<'_, 'tcx>) -> PcgNode<'tcx> {
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

    fn region_projections(self, ctxt: CompilerCtxt<'_, 'tcx>) -> Vec<LifetimeProjection<'tcx>> {
        match self {
            MaybeRemoteCurrentPlace::Local(place) => place
                .lifetime_projections(ctxt)
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
        loop_blocked_places: &PlaceUsages<'tcx>,
        root_places: HashSet<MaybeRemoteCurrentPlace<'tcx>>,
        candidate_blockers: &PlaceUsages<'tcx>,
        loop_head: mir::BasicBlock,
        validity_conditions: &ValidityConditions,
        analysis_ctxt: AnalysisCtxt<'mir, 'tcx>,
    ) -> ConstructAbstractionGraphResult<'tcx> {
        let ctxt = analysis_ctxt.ctxt;
        let mut graph = BorrowsGraph::default();
        let mut capability_updates = HashMap::default();
        let mut to_label = HashSet::default();

        let loop_head_location = mir::Location {
            block: loop_head,
            statement_index: 0,
        };

        let mut expander = AbsExpander {
            loop_head_block: loop_head,
            graph: &mut graph,
            validity_conditions,
            ctxt,
        };

        tracing::debug!(
            "loop blocked places: {}",
            loop_blocked_places.to_short_string(ctxt)
        );

        for blocker in candidate_blockers.iter_places() {
            for root in root_places.iter() {
                let relevant_root = root.relevant_place_for_blocking();
                if blocker == relevant_root
                    || ctxt
                        .bc
                        .blocks(blocker, relevant_root, loop_head_location, ctxt)
                {
                    tracing::debug!(
                        "{} blocks root {}",
                        blocker.to_short_string(ctxt),
                        relevant_root.to_short_string(ctxt)
                    );
                    add_block_edges(&mut expander, *root, blocker, ctxt);
                    if let MaybeRemoteCurrentPlace::Local(root) = root {
                        for rp in root.lifetime_projections(ctxt) {
                            to_label.insert(LabelLifetimeProjectionPredicate::AllNonFuture(
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

        for blocked_place_usage in loop_blocked_places.iter() {
            let blocked_place = blocked_place_usage.place;
            let blockers = candidate_blockers
                .iter_places()
                .filter(|blocker| {
                    blocker.local != blocked_place.local
                        && ctxt
                            .bc
                            .blocks(*blocker, blocked_place, loop_head_location, ctxt)
                })
                .collect::<Vec<_>>();
            if !blockers.is_empty() {
                for blocker in blockers.iter() {
                    add_block_edges(&mut expander, blocked_place.into(), *blocker, ctxt);
                }
                if blocked_place_usage.usage == PlaceUsageType::Mutate {
                    capability_updates.insert(blocked_place, None);
                } else {
                    capability_updates.insert(blocked_place, Some(CapabilityKind::Read));
                }
                for rp in blocked_place.lifetime_projections(ctxt) {
                    to_label.insert(LabelLifetimeProjectionPredicate::AllNonFuture(
                        blocked_place.into(),
                        rp.region_idx,
                    ));
                }
            }
        }
        expander.render_debug_graph(
            Some(DebugImgcat::JoinLoop),
            "Abstraction graph after connections expansion",
        );

        expander.expand_to_places(
            loop_blocked_places,
            &loop_blocked_places.joined_with(candidate_blockers),
        );

        expander.render_debug_graph(
            Some(DebugImgcat::JoinLoop),
            "Abstraction graph after expansion",
        );

        let abs_graph_roots = expander
            .graph
            .roots(ctxt)
            .into_iter()
            .flat_map(|graph_root| {
                if let Some(PcgNode::LifetimeProjection(rp)) = graph_root.try_to_local_node(ctxt)
                    && let MaybeLabelledPlace::Current(place) = rp.base
                    && !loop_blocked_places.contains(place)
                {
                    Some(rp)
                } else {
                    None
                }
            })
            .collect::<HashSet<_>>();

        for graph_root in abs_graph_roots {
            let mut candidate_root_nodes = self.nodes(ctxt);
            candidate_root_nodes.retain(|node| match node {
                PcgNode::LifetimeProjection(region_projection)
                    if let Some(related_place) =
                        region_projection.base.maybe_remote_current_place() =>
                {
                    root_places.contains(&related_place)
                }
                _ => false,
            });
            for node in candidate_root_nodes {
                if self
                    .nodes_blocked_by(graph_root.into(), ctxt)
                    .contains(&node)
                {
                    add_block_edge(&mut expander, node, graph_root.into(), ctxt);
                }
            }
        }

        expander.render_debug_graph(
            Some(DebugImgcat::JoinLoop),
            "Abstraction graph after root reconnect",
        );
        let loop_head_label = LifetimeProjectionLabel::Location(SnapshotLocation::Loop(loop_head));
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
        tracing::debug!("Completed loop abstraction");
        for (place, capability) in capability_updates.iter() {
            logging::log!(
                LogPredicate::DebugBlock,
                analysis_ctxt,
                "capability update for {}: {:?}",
                place.to_short_string(ctxt),
                capability
            );
        }
        ConstructAbstractionGraphResult::new(graph, to_label, capability_updates)
    }

    pub(crate) fn get_borrow_roots(
        &self,
        node: Place<'tcx>,
        loop_head_block: mir::BasicBlock,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> HashSet<PcgNode<'tcx>> {
        let mut result = HashSet::default();
        let mut queue: Vec<LocalNode<'tcx>> = node
            .lifetime_projections(ctxt)
            .into_iter()
            .flat_map(|rp| {
                vec![
                    rp.to_local_node(ctxt),
                    rp.with_label(
                        Some(LifetimeProjectionLabel::Location(SnapshotLocation::Loop(
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

    pub(crate) fn expand_places_for_abstraction<'a>(
        &mut self,
        loop_blocked_places: &PlaceUsages<'tcx>,
        to_expand: &PlaceUsages<'tcx>,
        validity_conditions: &ValidityConditions,
        args: JoinBorrowsArgs<'_, 'a, 'tcx>,
        ctxt: AnalysisCtxt<'a, 'tcx>,
    ) {
        let borrow = BorrowStateMutRef {
            graph: self,
            validity_conditions,
        };
        let pcg = PcgMutRef::new(args.owned, borrow, args.capabilities);
        let snapshot_location = SnapshotLocation::Loop(args.self_block);
        let mut obtainer = PlaceObtainer::new(
            pcg,
            None,
            ctxt,
            mir::Location {
                block: args.self_block,
                statement_index: 0,
            },
            snapshot_location,
        );
        let mut to_obtain: Vec<PlaceUsage<'tcx>> = vec![];
        for place_usage in to_expand.iter() {
            if to_obtain
                .iter()
                .any(|p| place_usage.place.is_prefix_of(p.place))
            {
                continue;
            }
            to_obtain.retain(|p| !place_usage.place.is_prefix_of(p.place));
            to_obtain.push(place_usage);
        }
        obtainer.render_debug_graph(Some(DebugImgcat::JoinLoop), "Before obtaining (self)");
        for place_usage in to_obtain {
            let obtain_type = ObtainType::LoopInvariant {
                is_blocked: loop_blocked_places.contains(place_usage.place),
                usage_type: place_usage.usage,
            };
            obtainer.obtain(place_usage.place, obtain_type).unwrap();
            obtainer.render_debug_graph(
                Some(DebugImgcat::JoinLoop),
                &format!(
                    "After obtaining (self) {}",
                    place_usage.to_short_string(ctxt.ctxt)
                ),
            );
        }
    }

    pub(crate) fn identify_subgraph_to_cut<'mir: 'graph, 'graph>(
        &'graph self,
        block: mir::BasicBlock,
        abstraction_graph_nodes: HashSet<PcgNode<'tcx>>,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> BorrowsGraph<'tcx> {
        type Path<'tcx, 'graph> = Vec<BorrowPcgEdgeRef<'tcx, 'graph>>;
        let mut to_cut = HashSet::default();
        let mut paths: Vec<Path<'tcx, 'graph>> = abstraction_graph_nodes
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
                        self.render_debug_graph(
                            block,
                            Some(DebugImgcat::JoinLoop),
                            &PlaceCapabilities::default(),
                            "Invalid abstraction graph",
                            ctxt,
                        );
                        pcg_validity_assert!(false, [ctxt], "edge already in path");
                        // panic!("edge already in path");
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
    validity_conditions: &'pcg ValidityConditions,
    ctxt: CompilerCtxt<'mir, 'tcx>,
}

impl RenderDebugGraph for AbsExpander<'_, '_, '_> {
    fn render_debug_graph(&self, debug_imgcat: Option<DebugImgcat>, comment: &str) {
        self.graph.render_debug_graph(
            self.loop_head_block,
            debug_imgcat,
            &PlaceCapabilities::default(),
            comment,
            self.ctxt,
        );
    }
}

impl<'tcx> AbsExpander<'_, '_, 'tcx> {
    fn loop_head_location(&self) -> mir::Location {
        mir::Location {
            block: self.loop_head_block,
            statement_index: 0,
        }
    }

    fn expand_to_places(&mut self, blocked_places: &PlaceUsages<'tcx>, places: &PlaceUsages<'tcx>) {
        for place in places.iter() {
            tracing::debug!("loop expanding to {}", place.to_short_string(self.ctxt));
            self.expand_to(
                place.place,
                ObtainType::LoopInvariant {
                    is_blocked: blocked_places.contains(place.place),
                    usage_type: place.usage,
                },
                self.ctxt,
            )
            .unwrap();
        }
    }
}

impl<'tcx> ActionApplier<'tcx> for AbsExpander<'_, '_, 'tcx> {
    fn apply_action(&mut self, action: PcgAction<'tcx>) -> Result<bool, crate::error::PcgError> {
        tracing::debug!("applying action: {}", action.debug_line(self.ctxt));
        match action {
            PcgAction::Borrow(action) => match action.kind {
                BorrowPcgActionKind::AddEdge { edge } => Ok(self.graph.insert(edge, self.ctxt)),
                BorrowPcgActionKind::LabelLifetimeProjection(
                    predicate,
                    region_projection_label,
                ) => Ok(self.graph.label_region_projection(
                    &predicate,
                    region_projection_label,
                    self.ctxt,
                )),
                BorrowPcgActionKind::Weaken(_) => todo!(),
                BorrowPcgActionKind::Restore(_) => todo!(),
                BorrowPcgActionKind::MakePlaceOld(_) => todo!(),
                BorrowPcgActionKind::RemoveEdge(borrow_pcg_edge) => {
                    self.graph.remove(borrow_pcg_edge.kind());
                    Ok(true)
                }
            },
            PcgAction::Owned(action) => match action.kind {
                RepackOp::StorageDead(_) => todo!(),
                RepackOp::IgnoreStorageDead(_) => todo!(),
                RepackOp::Weaken(_, _, _) => todo!(),
                RepackOp::Expand(_repack_expand) => {
                    unreachable!()
                }
                RepackOp::Collapse(_) => todo!(),
                RepackOp::DerefShallowInit(_, _) => todo!(),
                RepackOp::RegainLoanedCapability(_, _) => todo!(),
            },
        }
    }
}

impl<'mir, 'tcx> PlaceExpander<'mir, 'tcx> for AbsExpander<'_, 'mir, 'tcx> {
    fn borrows_graph(&self) -> &BorrowsGraph<'tcx> {
        self.graph
    }

    fn path_conditions(&self) -> ValidityConditions {
        self.validity_conditions.clone()
    }

    fn contains_owned_expansion_to(&self, _target: Place<'tcx>) -> bool {
        // Pretend we're always fully expanded in the local PCG
        true
    }

    fn update_capabilities_for_borrow_expansion(
        &mut self,
        _expansion: &crate::borrow_pcg::borrow_pcg_expansion::BorrowPcgExpansion<'tcx>,
        _block_type: crate::pcg::place_capabilities::BlockType,
        _ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<bool, crate::error::PcgError> {
        Ok(true)
    }
    fn update_capabilities_for_deref(
        &mut self,
        _ref_place: Place<'tcx>,
        _capability: CapabilityKind,
        _ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<bool, crate::error::PcgError> {
        Ok(true)
    }

    fn location(&self) -> mir::Location {
        self.loop_head_location()
    }
}

impl HasSnapshotLocation for AbsExpander<'_, '_, '_> {
    fn prev_snapshot_location(&self) -> SnapshotLocation {
        SnapshotLocation::Loop(self.loop_head_block)
    }
}

fn add_block_edge<'tcx, 'mir>(
    expander: &mut AbsExpander<'_, 'mir, 'tcx>,
    long: PcgNode<'tcx>,
    short: LocalNode<'tcx>,
    ctxt: CompilerCtxt<'mir, 'tcx>,
) {
    let long_edge = AbstractionBlockEdge::new(vec![long.into()], vec![short.into()], ctxt);
    let loop_edge = LoopAbstraction::new(long_edge, expander.loop_head_block);
    expander.graph.insert(
        loop_edge.to_borrow_pcg_edge(expander.validity_conditions.clone()),
        ctxt,
    );
}

fn add_rp_block_edges<'mir, 'tcx>(
    expander: &mut AbsExpander<'_, 'mir, 'tcx>,
    blocked_place: MaybeRemoteCurrentPlace<'tcx>,
    blocker: Place<'tcx>,
    ctxt: CompilerCtxt<'mir, 'tcx>,
) {
    let blocker_rps = blocker.lifetime_projections(ctxt);
    for blocked_rp in blocked_place.region_projections(ctxt) {
        let flow_rps = blocker_rps
            .iter()
            .filter(|blocker_rp| {
                ctxt.bc.outlives(
                    blocked_rp.region(ctxt),
                    blocker_rp.region(ctxt),
                    expander.loop_head_location(),
                )
            })
            .copied()
            .collect::<Vec<_>>();
        if let Some(blocked_node) = blocked_rp.try_to_local_node(ctxt) {
            let blocked_rp = blocked_node.try_into_region_projection().unwrap();
            let mut_rps = flow_rps
                .iter()
                .filter_map(|rp| {
                    if rp.is_invariant_in_type(ctxt)
                        && ctxt.bc.outlives(
                            rp.region(ctxt),
                            blocked_rp.region(ctxt),
                            expander.loop_head_location(),
                        )
                    {
                        Some(rp.rebase())
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>();
            if !mut_rps.is_empty() {
                tracing::debug!(
                    "Mutable rps: {} -> {}",
                    blocked_rp.to_short_string(ctxt),
                    mut_rps.to_short_string(ctxt)
                );
                expander
                    .add_and_update_placeholder_edges(blocked_rp, &mut_rps, "mut rps", ctxt)
                    .unwrap();
                expander.render_debug_graph(
                    Some(DebugImgcat::JoinLoop),
                    "Abstraction graph after adding mut rps",
                );
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
    assert_ne!(
        MaybeRemoteCurrentPlace::Local(blocker),
        blocked_place,
        "blocker {} and blocked_place {} are the same",
        blocker.to_short_string(ctxt),
        blocked_place.to_short_string(ctxt)
    );
    let blocker_rps = blocker.lifetime_projections(ctxt);
    // Add top-level borrow
    add_block_edge(
        expander,
        blocked_place.to_pcg_node(ctxt),
        blocker_rps[RegionIdx::from(0)].to_local_node(ctxt),
        ctxt,
    );
    add_rp_block_edges(expander, blocked_place, blocker, ctxt);
}
