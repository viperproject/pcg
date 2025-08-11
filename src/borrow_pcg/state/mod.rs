//! The data structure representing the state of the Borrow PCG.

use crate::rustc_interface::middle::mir::START_BLOCK;

use super::{
    borrow_pcg_edge::{BlockedNode, BorrowPcgEdge, BorrowPcgEdgeRef, ToBorrowsEdge},
    edge::borrow::RemoteBorrow,
    graph::BorrowsGraph,
    path_condition::{PathCondition, ValidityConditions},
    visitor::extract_regions,
};
use crate::{
    action::BorrowPcgAction,
    borrow_pcg::{
        action::{BorrowPcgActionKind, LabelPlaceReason},
        has_pcs_elem::{LabelLifetimeProjectionPredicate, PlaceLabeller, SetLabel},
        region_projection::LifetimeProjectionLabel,
    },
    free_pcs::OwnedPcg,
    pcg::{
        BodyAnalysis, PcgError, ctxt::AnalysisCtxt, place_capabilities::PlaceCapabilitiesInterface,
    },
    pcg_validity_assert,
    utils::{
        display::DisplayWithCompilerCtxt,
        logging::{self, LogPredicate},
        place::maybe_remote::MaybeRemotePlace,
    },
};
use crate::{
    borrow_pcg::edge::kind::BorrowPcgEdgeKind, utils::place::maybe_old::MaybeLabelledPlace,
};
use crate::{
    borrow_pcg::edge::{
        borrow::{BorrowEdge, LocalBorrow},
        outlives::BorrowFlowEdgeKind,
    },
    pcg::place_capabilities::PlaceCapabilities,
};
use crate::{
    borrow_pcg::edge_data::EdgeData,
    pcg::PcgNode,
    rustc_interface::middle::{
        mir::{self, BasicBlock, BorrowKind, Location, MutBorrowKind},
        ty::{self},
    },
    utils::{display::DebugLines, validity::HasValidityCheck},
};
use crate::{
    borrow_pcg::{edge::outlives::BorrowFlowEdge, region_projection::LifetimeProjection},
    utils::remote::RemotePlace,
};
use crate::{
    free_pcs::CapabilityKind,
    utils::{CompilerCtxt, Place},
};

/// The state of the Borrow PCG, including the Borrow PCG graph and the validity
/// conditions associated with the current basic block.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct BorrowsState<'tcx> {
    pub(crate) graph: BorrowsGraph<'tcx>,
    pub(crate) path_conditions: ValidityConditions,
}

pub(crate) struct BorrowStateMutRef<'pcg, 'tcx> {
    pub(crate) graph: &'pcg mut BorrowsGraph<'tcx>,
    pub(crate) path_conditions: &'pcg ValidityConditions,
}

#[allow(unused)]
#[derive(Clone, Copy)]
pub(crate) struct BorrowStateRef<'pcg, 'tcx> {
    pub(crate) graph: &'pcg BorrowsGraph<'tcx>,
    pub(crate) path_conditions: &'pcg ValidityConditions,
}

pub(crate) trait BorrowsStateLike<'tcx> {
    fn as_mut_ref(&mut self) -> BorrowStateMutRef<'_, 'tcx>;
    fn as_ref(&self) -> BorrowStateRef<'_, 'tcx>;

    fn graph_mut(&mut self) -> &mut BorrowsGraph<'tcx> {
        self.as_mut_ref().graph
    }
    fn graph(&self) -> &BorrowsGraph<'tcx>;

    fn label_place_and_update_related_capabilities(
        &mut self,
        place: Place<'tcx>,
        reason: LabelPlaceReason,
        labeller: &impl PlaceLabeller<'tcx>,
        capabilities: &mut PlaceCapabilities<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        let state = self.as_mut_ref();
        state.graph.label_place(place, reason, labeller, ctxt);
        // If in a join we don't want to change capabilities because this will
        // essentially be handled by the join logic.
        // See 69_http_header_map.rs
        if reason != LabelPlaceReason::JoinOwnedReadAndWriteCapabilities {
            capabilities.retain(|p, _| !p.projects_indirection_from(place, ctxt));
        }
        true
    }

    fn label_region_projection(
        &mut self,
        predicate: &LabelLifetimeProjectionPredicate<'tcx>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.graph_mut()
            .label_region_projection(predicate, label, ctxt)
    }

    fn remove<'a>(
        &mut self,
        edge: &BorrowPcgEdgeKind<'tcx>,
        capabilities: &mut PlaceCapabilities<'tcx>,
        ctxt: AnalysisCtxt<'a, 'tcx>,
    ) -> bool
    where
        'tcx: 'a,
    {
        let state = self.as_mut_ref();
        let removed = state.graph.remove(edge).is_some();
        if removed {
            for node in edge.blocked_by_nodes(ctxt.ctxt) {
                if !state.graph.contains(node, ctxt.ctxt)
                    && let PcgNode::Place(MaybeLabelledPlace::Current(place)) = node
                {
                    let _ = capabilities.remove(place, ctxt);
                }
            }
        }
        removed
    }

    fn apply_action(
        &mut self,
        action: BorrowPcgAction<'tcx>,
        capabilities: &mut PlaceCapabilities<'tcx>,
        ctxt: AnalysisCtxt<'_, 'tcx>,
    ) -> Result<bool, PcgError> {
        let result = match action.kind {
            BorrowPcgActionKind::Restore(restore) => {
                let restore_place = restore.place();
                if let Some(cap) = capabilities.get(restore_place, ctxt.ctxt) {
                    pcg_validity_assert!(
                        cap < restore.capability(),
                        "Current capability {:?} is not less than the capability to restore to {:?}",
                        cap,
                        restore.capability()
                    );
                }
                if !capabilities.insert(restore_place, restore.capability(), ctxt) {
                    panic!("Capability should have been updated")
                }
                if restore.capability() == CapabilityKind::Exclusive {
                    self.label_region_projection(
                        &LabelLifetimeProjectionPredicate::AllFuturePostfixes(restore_place),
                        None,
                        ctxt.ctxt,
                    );
                }
                true
            }
            BorrowPcgActionKind::Weaken(weaken) => {
                let weaken_place = weaken.place();
                assert_eq!(capabilities.get(weaken_place, ctxt.ctxt), Some(weaken.from));
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
            BorrowPcgActionKind::MakePlaceOld(action) => self
                .label_place_and_update_related_capabilities(
                    action.place,
                    action.reason,
                    &SetLabel(action.location),
                    capabilities,
                    ctxt.ctxt,
                ),
            BorrowPcgActionKind::RemoveEdge(edge) => self.remove(&edge.kind, capabilities, ctxt),
            BorrowPcgActionKind::AddEdge { edge } => self.graph_mut().insert(edge, ctxt.ctxt),
            BorrowPcgActionKind::LabelLifetimeProjection(rp, label) => {
                self.label_region_projection(&rp, label, ctxt.ctxt)
            }
        };
        Ok(result)
    }
}

impl<'pcg, 'tcx: 'pcg> BorrowsStateLike<'tcx> for BorrowStateMutRef<'pcg, 'tcx> {
    fn as_mut_ref(&mut self) -> BorrowStateMutRef<'_, 'tcx> {
        BorrowStateMutRef {
            graph: self.graph,
            path_conditions: self.path_conditions,
        }
    }

    fn graph(&self) -> &BorrowsGraph<'tcx> {
        self.graph
    }

    fn as_ref(&self) -> BorrowStateRef<'_, 'tcx> {
        BorrowStateRef {
            graph: self.graph,
            path_conditions: self.path_conditions,
        }
    }
}

impl<'tcx> BorrowsStateLike<'tcx> for BorrowsState<'tcx> {
    fn as_mut_ref(&mut self) -> BorrowStateMutRef<'_, 'tcx> {
        BorrowStateMutRef {
            graph: &mut self.graph,
            path_conditions: &self.path_conditions,
        }
    }

    fn graph(&self) -> &BorrowsGraph<'tcx> {
        &self.graph
    }

    fn as_ref(&self) -> BorrowStateRef<'_, 'tcx> {
        BorrowStateRef {
            graph: &self.graph,
            path_conditions: &self.path_conditions,
        }
    }
}

impl<'pcg, 'tcx> From<&'pcg mut BorrowsState<'tcx>> for BorrowStateMutRef<'pcg, 'tcx> {
    fn from(borrows_state: &'pcg mut BorrowsState<'tcx>) -> Self {
        Self {
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
        ctxt: AnalysisCtxt<'_, 'tcx>,
    ) {
        let local_decl = &ctxt.ctxt.body().local_decls[local];
        let arg_place: Place<'tcx> = local.into();
        if let ty::TyKind::Ref(_, _, _) = local_decl.ty.kind() {
            let _ = self.apply_action(
                BorrowPcgAction::add_edge(
                    BorrowPcgEdge::new(RemoteBorrow::new(local).into(), ValidityConditions::new()),
                    "Introduce initial borrows",
                    ctxt.ctxt,
                ),
                capabilities,
                ctxt,
            );
        }
        for region in extract_regions(local_decl.ty, ctxt.ctxt) {
            let region_projection =
                LifetimeProjection::new(region, arg_place.into(), None, ctxt.ctxt).unwrap();
            assert!(
                self.apply_action(
                    BorrowPcgAction::add_edge(
                        BorrowPcgEdge::new(
                            BorrowFlowEdge::new(
                                LifetimeProjection::new(
                                    region,
                                    RemotePlace::new(local).into(),
                                    None,
                                    ctxt.ctxt,
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
                                ctxt.ctxt,
                            )
                            .into(),
                            ValidityConditions::new(),
                        ),
                        "Introduce initial borrows",
                        ctxt.ctxt,
                    ),
                    capabilities,
                    ctxt,
                )
                .unwrap()
            );
        }
    }

    pub(crate) fn initialize_as_start_block(
        &mut self,
        capabilities: &mut PlaceCapabilities<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) {
        let analysis_ctxt = AnalysisCtxt::new(repacker, START_BLOCK);
        for arg in repacker.body().args_iter() {
            self.introduce_initial_borrows(arg, capabilities, analysis_ctxt);
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
        owned: &mut OwnedPcg<'tcx>,
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
            self.path_conditions.clone(),
            ctxt,
        )?;
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
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Option<MaybeLabelledPlace<'tcx>> {
        let edges = self.edges_blocking(place.into(), ctxt);
        if edges.len() != 1 {
            return None;
        }
        let nodes = edges[0].blocked_by_nodes(ctxt).collect::<Vec<_>>();
        if nodes.len() != 1 {
            return None;
        }
        let node = nodes.into_iter().next().unwrap();
        match node {
            PcgNode::Place(_) => todo!(),
            PcgNode::LifetimeProjection(region_projection) => region_projection.deref(ctxt),
        }
    }

    pub(crate) fn edges_blocking<'slf, 'mir: 'slf, 'bc: 'slf>(
        &'slf self,
        node: BlockedNode<'tcx>,
        repacker: CompilerCtxt<'mir, 'tcx>,
    ) -> Vec<BorrowPcgEdgeRef<'tcx, 'slf>> {
        self.graph.edges_blocking(node, repacker).collect()
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
        let ctxt = AnalysisCtxt::new(ctxt, location.block);
        logging::log!(
            LogPredicate::DebugBlock,
            ctxt,
            "Inserting borrow edge {}",
            borrow_edge.to_short_string(ctxt.ctxt)
        );
        assert!(self.graph.insert(
            BorrowEdge::Local(borrow_edge).to_borrow_pcg_edge(self.path_conditions.clone()),
            ctxt.ctxt
        ));

        match kind {
            BorrowKind::Mut {
                kind: MutBorrowKind::Default | MutBorrowKind::ClosureCapture,
            } => {
                let _ = capabilities.remove(blocked_place, ctxt);
            }
            _ => {
                let blocked_place_capability = capabilities.get(blocked_place, ctxt.ctxt);
                logging::log!(
                    LogPredicate::DebugBlock,
                    ctxt,
                    "Blocked place {} has capability {:?}",
                    blocked_place.to_short_string(ctxt.ctxt),
                    blocked_place_capability
                );
                match blocked_place_capability {
                    Some(CapabilityKind::Exclusive) => {
                        assert!(capabilities.insert(blocked_place, CapabilityKind::Read, ctxt));
                    }
                    Some(CapabilityKind::Read) => {
                        // Do nothing, this just adds another shared borrow
                    }
                    other => {
                        // Shouldn't be None or Write, due to capability updates
                        // based on the TripleWalker analysis
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
