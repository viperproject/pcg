//! The data structure representing the state of the Borrow PCG.

use super::{
    borrow_pcg_edge::{BlockedNode, BorrowPcgEdge, BorrowPcgEdgeRef, ToBorrowsEdge},
    edge::borrow::RemoteBorrow,
    graph::BorrowsGraph,
    latest::Latest,
    path_condition::{PathCondition, PathConditions},
    visitor::extract_regions,
};
use crate::{
    action::BorrowPcgAction,
    borrow_pcg::{action::{BorrowPcgActionKind, MakePlaceOldReason}, has_pcs_elem::LabelRegionProjectionPredicate, region_projection::RegionProjectionLabel},
    free_pcs::FreePlaceCapabilitySummary,
    pcg::{place_capabilities::PlaceCapabilitiesInterface, BodyAnalysis, PcgError},
    pcg_validity_assert,
    utils::place::maybe_remote::MaybeRemotePlace,
};
use crate::{borrow_pcg::borrow_pcg_edge::LocalNode, utils::place::maybe_old::MaybeOldPlace};
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
};
use crate::{
    borrow_pcg::{edge::outlives::BorrowFlowEdge, region_projection::RegionProjection},
    utils::remote::RemotePlace,
};
use crate::{
    free_pcs::CapabilityKind,
    utils::{CompilerCtxt, Place, SnapshotLocation},
};

/// The state of the Borrow PCG, including the Borrow PCG graph, the latest
/// locations of places, and the validity conditions associated with the current
/// basic block.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct BorrowsState<'tcx> {
    pub latest: Latest<'tcx>,
    pub(crate) graph: BorrowsGraph<'tcx>,
    pub(crate) path_conditions: PathConditions,
}

pub(crate) struct BorrowStateMutRef<'pcg, 'tcx> {
    pub(crate) latest: &'pcg mut Latest<'tcx>,
    pub(crate) graph: &'pcg mut BorrowsGraph<'tcx>,
    pub(crate) path_conditions: &'pcg PathConditions,
}

#[allow(unused)]
#[derive(Clone, Copy)]
pub(crate) struct BorrowStateRef<'pcg, 'tcx> {
    pub(crate) latest: &'pcg Latest<'tcx>,
    pub(crate) graph: &'pcg BorrowsGraph<'tcx>,
    pub(crate) path_conditions: &'pcg PathConditions,
}

pub(crate) trait BorrowsStateLike<'tcx> {
    fn as_mut_ref(&mut self) -> BorrowStateMutRef<'_, 'tcx>;
    fn as_ref(&self) -> BorrowStateRef<'_, 'tcx>;

    fn latest(&mut self) -> &mut Latest<'tcx> {
        self.as_mut_ref().latest
    }
    fn graph_mut(&mut self) -> &mut BorrowsGraph<'tcx> {
        self.as_mut_ref().graph
    }
    fn graph(&self) -> &BorrowsGraph<'tcx>;

    // fn path_conditions(&self) -> &PathConditions {
    //     self.as_ref().path_conditions
    // }

    fn leaf_nodes(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Vec<LocalNode<'tcx>> {
        self.graph().frozen_graph().leaf_nodes(ctxt)
    }

    fn set_latest(
        &mut self,
        place: Place<'tcx>,
        location: SnapshotLocation,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.latest().insert(place, location, ctxt)
    }

    fn make_place_old(
        &mut self,
        place: Place<'tcx>,
        reason: MakePlaceOldReason,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        let state = self.as_mut_ref();
        state
            .graph
            .make_place_old(place, reason, state.latest, ctxt)
    }

    fn label_region_projection(
        &mut self,
        predicate: &LabelRegionProjectionPredicate<'tcx>,
        label: Option<RegionProjectionLabel>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.graph_mut().label_region_projection(predicate, label, ctxt)
    }

    fn remove(
        &mut self,
        edge: &BorrowPcgEdge<'tcx>,
        capabilities: &mut PlaceCapabilities<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        let state = self.as_mut_ref();
        let removed = state.graph.remove(edge.kind()).is_some();
        if removed {
            for node in edge.blocked_by_nodes(repacker) {
                if !state.graph.contains(node, repacker)
                    && let PCGNode::Place(MaybeOldPlace::Current { place }) = node
                {
                    let _ = capabilities.remove(place, repacker);
                }
            }
        }
        removed
    }

    fn apply_action(
        &mut self,
        action: BorrowPcgAction<'tcx>,
        capabilities: &mut PlaceCapabilities<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<bool, PcgError> {
        let result = match action.kind {
            BorrowPcgActionKind::Restore(restore) => {
                let restore_place = restore.place();
                if let Some(cap) = capabilities.get(restore_place) {
                    assert!(cap < restore.capability(), "Current capability {:?} is not less than the capability to restore to {:?}", cap, restore.capability());
                }
                if !capabilities.insert(restore_place, restore.capability(), ctxt) {
                    panic!("Capability should have been updated")
                }
                true
            }
            BorrowPcgActionKind::Weaken(weaken) => {
                let weaken_place = weaken.place();
                assert_eq!(capabilities.get(weaken_place), Some(weaken.from));
                match weaken.to {
                    Some(to) => {
                        capabilities.insert(weaken_place, to, ctxt);
                    }
                    None => {
                        assert!(capabilities.remove(weaken_place, ctxt).is_some());
                    }
                }
                true
            }
            BorrowPcgActionKind::MakePlaceOld(place, reason) => {
                self.make_place_old(place, reason, ctxt)
            }
            BorrowPcgActionKind::SetLatest(place, location) => {
                self.set_latest(place, location, ctxt)
            }
            BorrowPcgActionKind::RemoveEdge(edge) => self.remove(&edge, capabilities, ctxt),
            BorrowPcgActionKind::AddEdge { edge } => self.graph_mut().insert(edge, ctxt),
            BorrowPcgActionKind::LabelRegionProjection(rp, label) => {
                self.label_region_projection(&rp, label, ctxt)
            }
        };
        Ok(result)
    }
}

impl<'pcg, 'tcx: 'pcg> BorrowsStateLike<'tcx> for BorrowStateMutRef<'pcg, 'tcx> {
    fn as_mut_ref(&mut self) -> BorrowStateMutRef<'_, 'tcx> {
        BorrowStateMutRef {
            latest: self.latest,
            graph: self.graph,
            path_conditions: self.path_conditions,
        }
    }

    fn graph(&self) -> &BorrowsGraph<'tcx> {
        self.graph
    }

    fn as_ref(&self) -> BorrowStateRef<'_, 'tcx> {
        BorrowStateRef {
            latest: self.latest,
            graph: self.graph,
            path_conditions: self.path_conditions,
        }
    }
}

impl<'tcx> BorrowsStateLike<'tcx> for BorrowsState<'tcx> {
    fn as_mut_ref(&mut self) -> BorrowStateMutRef<'_, 'tcx> {
        BorrowStateMutRef {
            latest: &mut self.latest,
            graph: &mut self.graph,
            path_conditions: &self.path_conditions,
        }
    }

    fn graph(&self) -> &BorrowsGraph<'tcx> {
        &self.graph
    }

    fn as_ref(&self) -> BorrowStateRef<'_, 'tcx> {
        BorrowStateRef {
            latest: &self.latest,
            graph: &self.graph,
            path_conditions: &self.path_conditions,
        }
    }
}

impl<'pcg, 'tcx> From<&'pcg mut BorrowsState<'tcx>> for BorrowStateMutRef<'pcg, 'tcx> {
    fn from(borrows_state: &'pcg mut BorrowsState<'tcx>) -> Self {
        Self {
            latest: &mut borrows_state.latest,
            graph: &mut borrows_state.graph,
            path_conditions: &borrows_state.path_conditions,
        }
    }
}

impl<'tcx> DebugLines<CompilerCtxt<'_, 'tcx>> for BorrowsState<'tcx> {
    fn debug_lines(&self, repacker: CompilerCtxt<'_, 'tcx>) -> Vec<String> {
        let mut lines = Vec::new();
        lines.extend(self.graph.debug_lines(repacker));
        lines
    }
}

impl<'tcx> HasValidityCheck<'tcx> for BorrowStateRef<'_, 'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        self.graph.check_validity(ctxt)?;
        Ok(())
    }
}

impl<'tcx> HasValidityCheck<'tcx> for BorrowStateMutRef<'_, 'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        self.as_ref().check_validity(ctxt)
    }
}

impl<'tcx> BorrowsState<'tcx> {
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
                BorrowPcgAction::add_edge(
                    BorrowPcgEdge::new(RemoteBorrow::new(local).into(), PathConditions::new()),
                    "Introduce initial borrows",
                    repacker,
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
                    BorrowPcgAction::add_edge(
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
                        "Introduce initial borrows",
                        repacker,
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

    pub fn graph(&self) -> &BorrowsGraph<'tcx> {
        &self.graph
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn join<'mir>(
        &mut self,
        other: &Self,
        self_block: BasicBlock,
        other_block: BasicBlock,
        body_analysis: &BodyAnalysis<'mir, 'tcx>,
        capabilities: &mut PlaceCapabilities<'tcx>,
        owned: &mut FreePlaceCapabilitySummary<'tcx>,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> Result<bool, PcgError> {
        let mut changed = false;
        changed |= self.graph.join(
            &other.graph,
            self_block,
            other_block,
            body_analysis,
            capabilities,
            owned,
            &mut self.latest,
            self.path_conditions.clone(),
            ctxt,
        )?;
        changed |= self.latest.join(&other.latest, self_block, ctxt);
        changed |= self
            .path_conditions
            .join(&other.path_conditions, ctxt.body());
        Ok(changed)
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

    /// Remove all edges that are not valid for `path`, based on their validity
    /// conditions.
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
    ) -> Vec<BorrowPcgEdgeRef<'tcx, 'slf>> {
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
        assert!(self.graph.insert(
            BorrowEdge::Local(borrow_edge).to_borrow_pcg_edge(self.path_conditions.clone()),
            ctxt
        ));

        match kind {
            BorrowKind::Mut {
                kind: MutBorrowKind::Default | MutBorrowKind::ClosureCapture,
            } => {
                let _ = capabilities.remove(blocked_place, ctxt);
            }
            _ => {
                match capabilities.get(blocked_place) {
                    Some(CapabilityKind::Exclusive) => {
                        assert!(capabilities.insert(blocked_place, CapabilityKind::Read, ctxt));
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
                        pcg_validity_assert!(
                            false,
                            "{:?}: Unexpected capability for borrow blocked place {:?}: {:?}",
                            location,
                            blocked_place,
                            other
                        );
                    }
                }
            }
        }
    }
}
