use std::cmp::Ordering;
use std::collections::HashSet;

use itertools::Itertools;

use crate::action::{ActionKindWithDebugCtxt, BorrowPcgAction, OwnedPcgAction, PcgAction};
use crate::borrow_pcg::action::{BorrowPcgActionKind, LabelPlaceReason};
use crate::borrow_pcg::borrow_pcg_edge::{BorrowPcgEdge, BorrowPcgEdgeLike};
use crate::borrow_pcg::borrow_pcg_expansion::{BorrowPcgExpansion, PlaceExpansion};
use crate::borrow_pcg::edge::deref::DerefEdge;
use crate::borrow_pcg::edge::kind::BorrowPcgEdgeKind;
use crate::borrow_pcg::edge::outlives::{BorrowFlowEdge, BorrowFlowEdgeKind};
use crate::borrow_pcg::edge_data::LabelPlacePredicate;
use crate::borrow_pcg::has_pcs_elem::{
    LabelLifetimeProjectionPredicate, LabelNodeContext, LabelPlace, LabelPlaceWithContext, SetLabel,
};
use crate::borrow_pcg::region_projection::{LifetimeProjection, LocalLifetimeProjection};
use crate::borrow_pcg::state::{BorrowStateMutRef, BorrowsStateLike};
use crate::free_pcs::{CapabilityKind, RepackGuide, RepackOp};
use crate::pcg::dot_graphs::{ToGraph, generate_dot_graph};
use crate::pcg::obtain::{
    ActionApplier, HasSnapshotLocation, ObtainType, PlaceCollapser, PlaceExpander, PlaceObtainer,
};
use crate::pcg::place_capabilities::{BlockType, PlaceCapabilitiesInterface};
use crate::pcg::{EvalStmtPhase, PCGNodeLike, PcgDebugData, PcgMutRef, PcgNode, PcgRefLike};
use crate::rustc_interface::middle::mir;
use crate::utils::display::DisplayWithCompilerCtxt;
use crate::utils::maybe_old::MaybeLabelledPlace;
use crate::utils::{CompilerCtxt, HasPlace};
use crate::{pcg_validity_assert, pcg_validity_expect_some};

use crate::utils::{Place, SnapshotLocation};

use super::{PcgError, PcgVisitor};
impl<'tcx> PcgVisitor<'_, '_, 'tcx> {
    pub(crate) fn place_obtainer(&mut self) -> PlaceObtainer<'_, '_, 'tcx> {
        let prev_snapshot_location = self.prev_snapshot_location();
        let pcg_ref = self.pcg.into();
        PlaceObtainer::new(
            pcg_ref,
            Some(&mut self.actions),
            self.ctxt,
            self.analysis_location.location,
            prev_snapshot_location,
            if let Some(debug_data) = &mut self.debug_data {
                Some(debug_data)
            } else {
                None
            },
        )
    }
    pub(crate) fn record_and_apply_action(
        &mut self,
        action: PcgAction<'tcx>,
    ) -> Result<bool, PcgError> {
        self.place_obtainer().record_and_apply_action(action)
    }
}

impl<'state, 'mir: 'state, 'tcx> PlaceCollapser<'mir, 'tcx> for PlaceObtainer<'state, 'mir, 'tcx> {
    fn get_local_expansions(&self, local: mir::Local) -> &crate::free_pcs::LocalExpansions<'tcx> {
        self.pcg.owned.locals()[local].get_allocated()
    }

    fn borrows_state(&mut self) -> BorrowStateMutRef<'_, 'tcx> {
        self.pcg.borrow.as_mut_ref()
    }

    fn capabilities(&mut self) -> &mut crate::pcg::place_capabilities::PlaceCapabilities<'tcx> {
        &mut self.pcg.capabilities
    }

    fn leaf_places(
        &self,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> crate::utils::data_structures::HashSet<Place<'tcx>> {
        let mut leaf_places = self.pcg.owned.leaf_places(ctxt);
        leaf_places.retain(|p| !self.pcg.borrow.graph().owned_places(ctxt).contains(p));
        leaf_places
    }
}

impl<'state, 'mir: 'state, 'tcx> PlaceObtainer<'state, 'mir, 'tcx> {
    fn update_unblocked_node_capabilities_and_remove_placeholder_projections(
        &mut self,
        edge: &impl BorrowPcgEdgeLike<'tcx>,
    ) -> Result<(), PcgError> {
        let fg = self.pcg.borrow.graph.frozen_graph();
        let blocked_nodes = edge.blocked_nodes(self.ctxt);

        // After removing an edge, some nodes may become accessible, their capabilities should be restored
        let to_restore = blocked_nodes
            .into_iter()
            .filter(|node| !fg.has_edge_blocking(*node, self.ctxt))
            .collect::<Vec<_>>();

        for node in to_restore {
            if let Some(place) = node.as_current_place() {
                let blocked_cap = self.pcg.capabilities.get(place);

                // TODO: If the place projects a shared ref, do we even need to restore a capability?
                let restore_cap = if place.place().projects_shared_ref(self.ctxt) {
                    CapabilityKind::Read
                } else {
                    CapabilityKind::Exclusive
                };

                // The blocked capability would be None if the place was mutably
                // borrowed The capability would be Write if the place is a
                // mutable reference (when dereferencing a mutable ref, the ref
                // place retains write capability)
                if blocked_cap.is_none() || matches!(blocked_cap, Some(CapabilityKind::Write)) {
                    self.record_and_apply_action(PcgAction::restore_capability(
                        place,
                        restore_cap,
                        "restore_capabilities_for_removed_edge",
                        self.ctxt,
                    ))?;
                }
                for rp in place.lifetime_projections(self.ctxt) {
                    self.record_and_apply_action(
                            BorrowPcgAction::remove_region_projection_label(
                                rp.with_placeholder_label(self.ctxt).into(),
                                format!(
                                    "Place {} unblocked: remove placeholder label of rps of newly unblocked nodes",
                                    place.to_short_string(self.ctxt)
                                ),
                            )
                            .into(),
                        )?;
                }
            }
        }
        Ok(())
    }

    /// If the following conditions apply:
    /// 1. `expansion` is a dereference of a place `p`
    /// 2. `*p` does not contain any borrows
    /// 3. The target of this expansion is not labelled
    ///
    /// Then we perform an optimization where instead of connecting the blocked
    /// lifetime projection to the current one, we instead remove the label of
    /// the blocked lifetime projection.
    ///
    /// This is sound because the lifetime projection only contains the single
    /// borrow that `p` refers to and therefore the set of borrows cannot be
    /// changed. In other words, the set of borrows in the lifetime projection
    /// at the point it was dereferenced is the same as the current set of
    /// borrows in the lifetime projection.
    ///
    /// Note the third condition: if the expansion is labelled, that indicates
    /// that the expansion occurred at a point where `p` had a different value
    /// than the current one. We don't want to perform this optimization because
    /// the it is referring to this different value.
    /// For test case see rustls-pki-types@1.11.0 server_name::parser::Parser::<'a>::read_char
    ///
    /// TODO: In the above test case, should the parent place also be labelled?
    fn unlabel_blocked_region_projections_if_applicable(
        &mut self,
        deref: &DerefEdge<'tcx>,
        context: &str,
    ) -> Result<(), PcgError> {
        // Check if the target is labelled e.g. *p @ l instead of *p
        if deref.deref_place.is_current() {
            self.unlabel_blocked_region_projections(deref, context)
        } else {
            Ok(())
        }
    }

    #[tracing::instrument(skip(self, edge))]
    pub(crate) fn remove_edge_and_perform_associated_state_updates(
        &mut self,
        edge: impl BorrowPcgEdgeLike<'tcx>,
        context: &str,
    ) -> Result<(), PcgError> {
        self.record_and_apply_action(
            BorrowPcgAction::remove_edge(edge.clone().to_owned_edge(), context).into(),
        )?;

        // This is true iff the expansion is for a place (not a region projection), and changes
        // could have been made to the root place via the expansion
        // We check that the base is place and either:
        // - The base has no capability, meaning it was previously expanded mutably
        // - The base has write capability, it is a mutable ref
        let is_mutable_place_expansion = if let BorrowPcgEdgeKind::BorrowPcgExpansion(expansion) =
            edge.kind()
            && let Some(place) = expansion.base.as_current_place()
        {
            matches!(
                self.pcg.capabilities.get(place),
                Some(CapabilityKind::Write) | None
            )
        } else {
            false
        };

        self.update_unblocked_node_capabilities_and_remove_placeholder_projections(&edge)?;

        match edge.kind() {
            BorrowPcgEdgeKind::Deref(deref) => {
                self.unlabel_blocked_region_projections_if_applicable(deref, context)?;
                if deref.deref_place.is_current() {
                    self.apply_action(
                        BorrowPcgAction::label_place(
                            deref.deref_place.place(),
                            self.prev_snapshot_location().into(),
                            LabelPlaceReason::Collapse,
                        )
                        .into(),
                    )?;
                }
            }
            BorrowPcgEdgeKind::BorrowPcgExpansion(expansion) => {
                if is_mutable_place_expansion {
                    // If the expansion contained region projections, we need to
                    // label them, they will flow into the now unblocked
                    // projection (i.e. the one obtained by removing the
                    // placeholder label)

                    // For example, if we a are packing *s.i into *s at l
                    // we need to label *s.i|'s to  *s|'s at l
                    // because we will remove the label from *s|'s at l'
                    // to become *s|'s. Otherwise we'd have both *s|'s and *s.i|'s
                    for exp_node in expansion.expansion() {
                        if let PcgNode::Place(place) = exp_node {
                            for rp in place.region_projections(self.ctxt) {
                                tracing::debug!(
                                    "labeling region projection: {}",
                                    rp.to_short_string(self.ctxt)
                                );
                                self.record_and_apply_action(
                                    BorrowPcgAction::label_lifetime_projection(
                                        LabelLifetimeProjectionPredicate::Equals(rp),
                                        Some(self.prev_snapshot_location().into()),
                                        format!(
                                            "{}: {}",
                                            context, "Label region projections of expansion"
                                        ),
                                    )
                                    .into(),
                                )?;
                            }
                        }
                    }
                }
            }
            BorrowPcgEdgeKind::Borrow(borrow) => {
                if self.ctxt.bc.is_dead(
                    borrow
                        .assigned_lifetime_projection(self.ctxt)
                        .to_pcg_node(self.ctxt),
                    self.location(),
                ) && let MaybeLabelledPlace::Current(place) = borrow.assigned_ref()
                    && let Some(existing_cap) = self.pcg.capabilities.get(place)
                {
                    self.record_and_apply_action(
                        BorrowPcgAction::weaken(
                            place,
                            existing_cap,
                            Some(CapabilityKind::Write),
                            "remove borrow edge",
                            self.ctxt,
                        )
                        .into(),
                    )?;
                }
            }
            _ => {}
        }
        Ok(())
    }

    /// As an optimization, for expansions of the form {y, y|'y at l} -> *y,
    /// if *y doesn't contain any borrows, we currently don't introduce placeholder
    /// projections for y|'y: the set of borrows is guaranteed not to change as long as *y
    /// is in the graph.
    ///
    /// Accordingly, when we want to remove *y in such cases, we just remove the
    /// label rather than use the normal logic (of renaming the placeholder
    /// projection to the current one).
    fn unlabel_blocked_region_projections(
        &mut self,
        deref: &DerefEdge<'tcx>,
        context: &str,
    ) -> Result<(), PcgError> {
        self.record_and_apply_action(
            BorrowPcgAction::remove_region_projection_label(
                deref.blocked_lifetime_projection(self.ctxt),
                format!("{}: unlabel blocked_region_projections", context),
            )
            .into(),
        )?;
        Ok(())
    }

    pub(crate) fn remove_read_permission_downwards(
        &mut self,
        upgraded_place: Place<'tcx>,
    ) -> Result<(), PcgError> {
        let to_remove = self
            .pcg
            .capabilities
            .iter()
            .filter(|(p, _)| {
                p.projection.len() > upgraded_place.projection.len()
                    && upgraded_place.is_prefix_of(*p)
            })
            .collect::<Vec<_>>();
        for (p, cap) in to_remove {
            self.record_and_apply_action(
                BorrowPcgAction::weaken(
                    p,
                    cap,
                    None,
                    "Remove read permission downwards",
                    self.ctxt,
                )
                .into(),
            )?;
        }
        Ok(())
    }

    pub(crate) fn upgrade_read_to_exclusive(&mut self, place: Place<'tcx>) -> Result<(), PcgError> {
        tracing::debug!(
            "upgrade_read_to_exclusive: {}",
            place.to_short_string(self.ctxt)
        );
        self.record_and_apply_action(
            BorrowPcgAction::restore_capability(
                place,
                CapabilityKind::Exclusive,
                "upgrade_read_to_exclusive",
            )
            .into(),
        )?;
        self.remove_read_permission_downwards(place)?;
        if let Some(parent) = place.parent_place() {
            self.remove_read_permission_upwards_and_label_rps(parent, "Upgrade read to exclusive")?;
        }
        Ok(())
    }

    pub(crate) fn new(
        pcg: PcgMutRef<'state, 'tcx>,
        actions: Option<&'state mut Vec<PcgAction<'tcx>>>,
        ctxt: CompilerCtxt<'mir, 'tcx>,
        location: mir::Location,
        prev_snapshot_location: SnapshotLocation,
        debug_data: Option<&'state mut PcgDebugData>,
    ) -> Self {
        Self {
            pcg,
            ctxt,
            actions,
            location,
            prev_snapshot_location,
            debug_data,
        }
    }

    // This function is called if we want to obtain non-read capability to `place`
    // If the closest ancestor of `place` has read capability, then we are allowed to
    // upgrade the capability of the ancestor to `E` in exchange for downgrading all
    // other pre / postfix places to None.
    //
    // This is sound because if we need to obtain non-read capability to
    // `place`, and there are any ancestors of `place` in the graph with R
    // capability, one such ancestor originally had E capability was
    // subsequently downgraded. This function finds such an ancestor (if one
    // exists), and performs the capability exchange.
    pub(crate) fn upgrade_closest_read_ancestor_to_exclusive_and_update_rps(
        &mut self,
        place: Place<'tcx>,
    ) -> Result<(), PcgError> {
        let mut expand_root = place;
        loop {
            if let Some(cap) = self.pcg.capabilities.get(expand_root) {
                if cap.is_read() {
                    self.upgrade_read_to_exclusive(expand_root)?;
                }
                return Ok(());
            }
            if let Some(parent) = expand_root.parent_place() {
                expand_root = parent;
            } else {
                return Ok(());
            }
        }
    }

    pub(crate) fn record_and_apply_action(
        &mut self,
        action: PcgAction<'tcx>,
    ) -> Result<bool, PcgError> {
        tracing::debug!("Applying Action: {}", action.debug_line(self.ctxt));
        let result = match &action {
            PcgAction::Borrow(action) => {
                self.pcg
                    .borrow
                    .apply_action(action.clone(), self.pcg.capabilities, self.ctxt)?
            }
            PcgAction::Owned(owned_action) => match owned_action.kind {
                RepackOp::RegainLoanedCapability(place, capability_kind) => {
                    self.pcg.capabilities.regain_loaned_capability(
                        place,
                        capability_kind,
                        self.pcg.borrow.as_mut_ref(),
                        self.ctxt,
                    )?;
                    true
                }
                RepackOp::Expand(expand) => {
                    self.pcg.owned.perform_expand_action(
                        expand,
                        self.pcg.capabilities,
                        self.ctxt,
                    )?;
                    true
                }
                RepackOp::DerefShallowInit(from, to) => {
                    let target_places = from.expand_one_level(to, self.ctxt)?.expansion();
                    let capability_projections =
                        self.pcg.owned.locals_mut()[from.local].get_allocated_mut();
                    capability_projections.insert_expansion(
                        from,
                        PlaceExpansion::from_places(target_places.clone(), self.ctxt),
                    );
                    for target_place in target_places {
                        self.pcg
                            .capabilities
                            .insert(target_place, CapabilityKind::Read, self.ctxt);
                    }
                    true
                }
                RepackOp::Collapse(collapse) => {
                    let capability_projections =
                        self.pcg.owned.locals_mut()[collapse.local()].get_allocated_mut();
                    capability_projections.perform_collapse_action(
                        collapse,
                        self.pcg.capabilities,
                        self.ctxt,
                    )?;
                    true
                }
                _ => unreachable!(),
            },
        };
        let location = self.location();

        if let Some(phase) = self.phase()
            && let Some(actions) = &mut self.actions
        {
            generate_dot_graph(
                location.block,
                location.statement_index,
                ToGraph::Action(phase, actions.len()),
                self.pcg.as_ref(),
                self.debug_data.as_deref(),
                self.ctxt,
            );
            actions.push(action);
        }
        Ok(result)
    }
    pub(crate) fn phase(&self) -> Option<EvalStmtPhase> {
        match self.prev_snapshot_location {
            SnapshotLocation::Before(analysis_location) => Some(analysis_location.eval_stmt_phase),
            _ => None,
        }
    }
}

impl<'state, 'mir: 'state, 'tcx> ActionApplier<'tcx> for PlaceObtainer<'state, 'mir, 'tcx> {
    fn apply_action(&mut self, action: PcgAction<'tcx>) -> Result<bool, PcgError> {
        self.record_and_apply_action(action)
    }
}

impl<'state, 'mir: 'state, 'tcx> PlaceObtainer<'state, 'mir, 'tcx> {
    /// Ensures that the place is expanded to the given place, with a certain
    /// capability.
    ///
    /// This also handles corresponding region projections of the place.
    pub(crate) fn obtain(
        &mut self,
        place: Place<'tcx>,
        obtain_type: ObtainType,
    ) -> Result<(), PcgError> {
        // This is to support the following kind of scenario:
        //
        //  - `s` is to be re-assigned or borrowed mutably at location `l`
        //  - `s.f` is shared a reference with lifetime 'a reborrowed into `x`
        //
        // We want to label s.f. such that the edge {s.f@l, s.f|'a@l} ->
        // {*s.f@l} is in the graph and redirect the borrow from *s.f to
        // *s.f@l
        //
        // After performing this operation, we should try again to remove borrow
        // PCG edges blocking `place`, since this may enable some borrow
        // expansions to be removed (s.f was previously blocked and no longer is)
        if !matches!(obtain_type, ObtainType::Capability(CapabilityKind::Read)) {
            self.label_and_remove_capabilities_for_shared_deref_projections_of_postfix_places(
                place, self.ctxt,
            )?;
            self.pack_old_and_dead_borrow_leaves(Some(place))?;
        }

        let obtain_cap = obtain_type.capability(place, self.ctxt);

        if !obtain_cap.is_read() {
            tracing::debug!(
                "Obtain {:?} to place {} in phase {:?}",
                obtain_type,
                place.to_short_string(self.ctxt),
                self.phase()
            );
            // It's possible that we want to obtain exclusive or write permission to
            // a field that we currently only have read access for. For example,
            // consider the following case:
            //
            // There is an existing shared borrow of (*c).f1
            // Therefore we have read permission to *c, (*c).f1, and (*c).f2
            // Then, we want to create a mutable borrow of (*c).f2
            // This requires obtaining exclusive permission to (*c).f2
            //
            // We can upgrade capability of (*c).f2 from R to E by downgrading all
            // other pre-and postfix places of (*c).f2 to None (in this case c and
            // *c). In the example, (*c).f2 is actually the closest read ancestor,
            // but this is not always the case (e.g. if we wanted to obtain
            // (*c).f2.f3 instead)
            //
            // This also labels rps and adds placeholder projections
            self.upgrade_closest_read_ancestor_to_exclusive_and_update_rps(place)?;
        }

        let current_cap = self.pcg.capabilities.get(place);

        if current_cap.is_none()
            || matches!(
                current_cap.unwrap().partial_cmp(&obtain_cap),
                Some(Ordering::Less) | None
            )
        {
            self.collapse_owned_places_to(
                place,
                obtain_cap,
                format!("Obtain {}", place.to_short_string(self.ctxt)),
                self.ctxt,
            )?;
        }

        if obtain_cap.is_write() {
            let _ = self.record_and_apply_action(
                BorrowPcgAction::label_place(
                    place,
                    self.prev_snapshot_location(),
                    LabelPlaceReason::ReAssign,
                )
                .into(),
            );
        }

        self.expand_to(place, obtain_type, self.ctxt)?;

        // pcg_validity_assert!(
        //     self.pcg.capabilities.get(place.into()).is_some(),
        //     "{:?}: Place {:?} does not have a capability after obtain {:?}",
        //     self.location,
        //     place,
        //     obtain_type.capability()
        // );
        // pcg_validity_assert!(
        //     self.pcg.capabilities.get(place.into()).unwrap() >= capability,
        //     "{:?} Capability {:?} for {:?} is not greater than {:?}",
        //     location,
        //     self.pcg.capabilities.get(place.into()).unwrap(),
        //     place,
        //     capability
        // );
        Ok(())
    }
}

impl<'pcg, 'mir: 'pcg, 'tcx> PlaceExpander<'mir, 'tcx> for PlaceObtainer<'pcg, 'mir, 'tcx> {
    fn contains_owned_expansion_to(&self, target: Place<'tcx>) -> bool {
        self.pcg.owned.locals()[target.local]
            .get_allocated()
            .contains_expansion_to(target, self.ctxt)
    }

    fn borrows_graph(&self) -> &crate::borrow_pcg::graph::BorrowsGraph<'tcx> {
        self.pcg.borrow.graph
    }

    fn path_conditions(&self) -> crate::borrow_pcg::path_condition::ValidityConditions {
        self.pcg.borrow.path_conditions.clone()
    }

    fn update_capabilities_for_borrow_expansion(
        &mut self,
        expansion: &BorrowPcgExpansion<'tcx>,
        block_type: BlockType,
        ctxt: crate::utils::CompilerCtxt<'_, 'tcx>,
    ) -> Result<bool, PcgError> {
        self.pcg
            .capabilities
            .update_for_expansion(expansion, block_type, ctxt)
    }

    fn location(&self) -> mir::Location {
        self.location
    }

    fn update_capabilities_for_deref(
        &mut self,
        ref_place: Place<'tcx>,
        capability: CapabilityKind,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<bool, PcgError> {
        self.pcg
            .capabilities
            .update_for_deref(ref_place, capability, ctxt)
    }
}
