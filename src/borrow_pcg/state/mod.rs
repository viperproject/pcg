use super::{
    action::BorrowPCGAction,
    borrow_pcg_edge::{BlockedNode, BorrowPCGEdgeRef, BorrowPcgEdge, ToBorrowsEdge},
    edge::borrow::RemoteBorrow,
    graph::BorrowsGraph,
    has_pcs_elem::LabelRegionProjection,
    latest::Latest,
    path_condition::{PathCondition, PathConditions},
    region_projection::RegionProjectionLabel,
    visitor::extract_regions,
};
use crate::utils::place::maybe_old::MaybeOldPlace;
use crate::utils::place::maybe_remote::MaybeRemotePlace;
use crate::{
    borrow_pcg::edge::{
        borrow::{BorrowEdge, LocalBorrow},
        outlives::BorrowFlowEdgeKind,
    },
    pcg::place_capabilities::PlaceCapabilities,
};
use crate::{
    borrow_pcg::edge_data::EdgeData,
    pcg::PCGNode,
    rustc_interface::middle::{
        mir::{self, BasicBlock, BorrowKind, Location, MutBorrowKind},
        ty::{self},
    },
    utils::{display::DebugLines, validity::HasValidityCheck},
    validity_checks_enabled,
};
use crate::{
    borrow_pcg::{edge::outlives::BorrowFlowEdge, region_projection::RegionProjection},
    utils::remote::RemotePlace,
};
use crate::{
    free_pcs::CapabilityKind,
    utils::{CompilerCtxt, Place, SnapshotLocation},
};

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct BorrowsState<'tcx> {
    pub latest: Latest<'tcx>,
    pub(crate) graph: BorrowsGraph<'tcx>,
    pub(crate) path_conditions: PathConditions,
}

impl<'tcx> DebugLines<CompilerCtxt<'_, 'tcx>> for BorrowsState<'tcx> {
    fn debug_lines(&self, repacker: CompilerCtxt<'_, 'tcx>) -> Vec<String> {
        let mut lines = Vec::new();
        lines.extend(self.graph.debug_lines(repacker));
        lines
    }
}

impl<'tcx> HasValidityCheck<'tcx> for BorrowsState<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        self.graph.check_validity(ctxt)
    }
}

impl<'tcx> BorrowsState<'tcx> {
    pub(crate) fn label_region_projection(
        &mut self,
        projection: &RegionProjection<'tcx, MaybeOldPlace<'tcx>>,
        label: Option<RegionProjectionLabel>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) {
        self.graph
            .mut_edges(|edge| edge.label_region_projection(projection, label, repacker));
    }
    fn introduce_initial_borrows(
        &mut self,
        local: mir::Local,
        capabilities: &mut PlaceCapabilities<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) {
        let local_decl = &repacker.body().local_decls[local];
        let arg_place: Place<'tcx> = local.into();
        if let ty::TyKind::Ref(_, _, _) = local_decl.ty.kind() {
            let _ = self.apply_action(
                BorrowPCGAction::add_edge(
                    BorrowPcgEdge::new(RemoteBorrow::new(local).into(), PathConditions::new()),
                    false,
                ),
                capabilities,
                repacker,
            );
        }
        for region in extract_regions(local_decl.ty, repacker) {
            let region_projection =
                RegionProjection::new(region, arg_place.into(), None, repacker).unwrap();
            assert!(self
                .apply_action(
                    BorrowPCGAction::add_edge(
                        BorrowPcgEdge::new(
                            BorrowFlowEdge::new(
                                RegionProjection::new(
                                    region,
                                    RemotePlace::new(local).into(),
                                    None,
                                    repacker,
                                )
                                .unwrap_or_else(|e| {
                                    panic!(
                                        "Failed to create region for remote place (for {local:?}).
                                    Local ty: {:?}. Error: {:?}",
                                        local_decl.ty, e
                                    );
                                }),
                                region_projection,
                                BorrowFlowEdgeKind::InitialBorrows,
                                repacker,
                            )
                            .into(),
                            PathConditions::new(),
                        ),
                        false,
                    ),
                    capabilities,
                    repacker,
                )
                .unwrap());
        }
    }

    pub(crate) fn initialize_as_start_block(
        &mut self,
        capabilities: &mut PlaceCapabilities<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) {
        for arg in repacker.body().args_iter() {
            self.introduce_initial_borrows(arg, capabilities, repacker);
        }
    }

    pub(crate) fn insert(
        &mut self,
        edge: BorrowPcgEdge<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.graph.insert(edge, ctxt)
    }

    pub(super) fn remove(
        &mut self,
        edge: &BorrowPcgEdge<'tcx>,
        capabilities: &mut PlaceCapabilities<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        let removed = self.graph.remove(edge.kind());
        if removed {
            for node in edge.blocked_by_nodes(repacker) {
                if !self.graph.contains(node, repacker)
                    && let PCGNode::Place(MaybeOldPlace::Current { place }) = node
                {
                    let _ = capabilities.remove(place.into());
                }
            }
        }
        removed
    }

    pub fn graph(&self) -> &BorrowsGraph<'tcx> {
        &self.graph
    }

    pub(crate) fn join<'mir>(
        &mut self,
        other: &Self,
        self_block: BasicBlock,
        other_block: BasicBlock,
        capabilities: &PlaceCapabilities<'tcx>,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> bool {
        let mut changed = false;
        changed |= self.graph.join(&other.graph, self_block, other_block, capabilities, ctxt);
        changed |= self.latest.join(&other.latest, self_block, ctxt);
        changed |= self
            .path_conditions
            .join(&other.path_conditions, ctxt.body());
        changed
    }

    pub(crate) fn add_cfg_edge(
        &mut self,
        from: BasicBlock,
        to: BasicBlock,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        if ctxt.is_back_edge(from, to) {
            return false;
        }
        let pc = PathCondition::new(from, to);
        self.path_conditions.insert(pc, ctxt.body());
        self.graph.add_path_condition(pc, ctxt)
    }

    pub fn filter_for_path(&mut self, path: &[BasicBlock], ctxt: CompilerCtxt<'_, 'tcx>) {
        self.graph.filter_for_path(path, ctxt);
    }

    /// Returns the place that blocks `place` if:
    /// 1. there is exactly one hyperedge blocking `place`
    /// 2. that edge is blocked by exactly one node
    /// 3. that node is a region projection that can be dereferenced
    ///
    /// This is used in the symbolic-execution based purification encoding to
    /// compute the backwards function for the argument local `place`. It
    /// depends on `Borrow` edges connecting the remote input to a single node
    /// in the PCG. In the symbolic execution, backward function results are computed
    /// per-path, so this expectation may be reasonable in that context.
    pub fn get_place_blocking(
        &self,
        place: MaybeRemotePlace<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> Option<MaybeOldPlace<'tcx>> {
        let edges = self.edges_blocking(place.into(), repacker);
        if edges.len() != 1 {
            return None;
        }
        let nodes = edges[0].blocked_by_nodes(repacker).collect::<Vec<_>>();
        if nodes.len() != 1 {
            return None;
        }
        let node = nodes.into_iter().next().unwrap();
        match node {
            PCGNode::Place(_) => todo!(),
            PCGNode::RegionProjection(region_projection) => region_projection.deref(repacker),
        }
    }

    pub(crate) fn edges_blocking<'slf, 'mir: 'slf, 'bc: 'slf>(
        &'slf self,
        node: BlockedNode<'tcx>,
        repacker: CompilerCtxt<'mir, 'tcx>,
    ) -> Vec<BorrowPCGEdgeRef<'tcx, 'slf>> {
        self.graph.edges_blocking(node, repacker).collect()
    }

    pub(crate) fn get_latest(
        &self,
        place: Place<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> SnapshotLocation {
        self.latest.get(place, ctxt)
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn add_borrow(
        &mut self,
        blocked_place: Place<'tcx>,
        assigned_place: Place<'tcx>,
        kind: BorrowKind,
        location: Location,
        region: ty::Region<'tcx>,
        capabilities: &mut PlaceCapabilities<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) {
        assert!(
            assigned_place.ty(ctxt).ty.ref_mutability().is_some(),
            "{:?}:{:?} Assigned place {:?} is not a reference. Ty: {:?}",
            ctxt.body().source.def_id(),
            location,
            assigned_place,
            assigned_place.ty(ctxt).ty
        );
        let borrow_edge = LocalBorrow::new(
            blocked_place.into(),
            assigned_place.into(),
            kind,
            location,
            region,
            ctxt,
        );
        // capabilities.insert(rp.place(), assigned_cap);
        assert!(self.graph.insert(
            BorrowEdge::Local(borrow_edge).to_borrow_pcg_edge(self.path_conditions.clone()),
            ctxt
        ));

        match kind {
            BorrowKind::Mut {
                kind: MutBorrowKind::Default,
            } => {
                let _ = capabilities.remove(blocked_place);
            }
            _ => {
                match capabilities.get(blocked_place) {
                    Some(CapabilityKind::Exclusive) => {
                        assert!(capabilities.insert(blocked_place, CapabilityKind::Read));
                    }
                    Some(CapabilityKind::Read) => {
                        // Do nothing, this just adds another shared borrow
                    }
                    None => {
                        // Some projections are currently incomplete (e.g. ConstantIndex)
                        // therefore we don't expect a capability here. For more information
                        // see the comment in `Place::expand_one_level`.
                        // TODO: Make such projections complete
                    }
                    other => {
                        if validity_checks_enabled() {
                            unreachable!(
                                "{:?}: Unexpected capability for borrow blocked place {:?}: {:?}",
                                location, blocked_place, other
                            );
                        }
                    }
                }
            }
        }
    }

    #[must_use]
    pub(crate) fn make_place_old(
        &mut self,
        place: Place<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.graph.make_place_old(place, &self.latest, ctxt)
    }
}
