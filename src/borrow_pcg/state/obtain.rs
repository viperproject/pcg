use crate::borrow_pcg::action::executed_actions::ExecutedActions;
use crate::borrow_pcg::action::BorrowPCGAction;
use crate::borrow_pcg::borrow_pcg_edge::{BorrowPCGEdge, LocalNode};
use crate::borrow_pcg::borrow_pcg_expansion::{BorrowPCGExpansion, PlaceExpansion};
use crate::borrow_pcg::edge::kind::BorrowPCGEdgeKind;
use crate::borrow_pcg::edge_data::EdgeData;
use crate::borrow_pcg::path_condition::PathConditions;
use crate::borrow_pcg::region_projection::RegionProjection;
use crate::borrow_pcg::state::BorrowsState;
use crate::free_pcs::CapabilityKind;
use crate::pcg::place_capabilities::PlaceCapabilities;
use crate::pcg::PcgError;
use crate::pcg_validity_assert;
use crate::rustc_interface::middle::mir::{BorrowKind, Location, MutBorrowKind};
use crate::rustc_interface::middle::ty::Mutability;
use crate::utils::maybe_old::MaybeOldPlace;
use crate::utils::{CompilerCtxt, HasPlace, Place, SnapshotLocation};

impl ObtainReason {
    /// After calling `obtain` for a place, the minimum capability that we
    /// expect the place to have.
    pub(crate) fn min_post_obtain_capability(&self) -> CapabilityKind {
        match self {
            ObtainReason::MoveOperand => CapabilityKind::Exclusive,
            ObtainReason::CopyOperand => CapabilityKind::Read,
            ObtainReason::FakeRead => CapabilityKind::Read,
            ObtainReason::AssignTarget => CapabilityKind::Write,
            ObtainReason::CreateReference(borrow_kind) => match borrow_kind {
                BorrowKind::Shared => CapabilityKind::Read,
                BorrowKind::Fake(_) => unreachable!(),
                BorrowKind::Mut { kind } => match kind {
                    MutBorrowKind::Default => CapabilityKind::Exclusive,
                    MutBorrowKind::TwoPhaseBorrow => CapabilityKind::Read,
                    MutBorrowKind::ClosureCapture => CapabilityKind::Exclusive,
                },
            },
            ObtainReason::CreatePtr(mutability) => {
                if mutability.is_mut() {
                    CapabilityKind::Exclusive
                } else {
                    CapabilityKind::Read
                }
            }
            ObtainReason::RValueSimpleRead => CapabilityKind::Read,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum ObtainReason {
    MoveOperand,
    CopyOperand,
    FakeRead,
    AssignTarget,
    CreateReference(BorrowKind),
    CreatePtr(Mutability),
    /// Just to read the place, but not refer to it
    RValueSimpleRead,
}

impl<'tcx> BorrowsState<'tcx> {
    /// Ensures that the place is expanded to the given place, with a certain
    /// capability.
    ///
    /// This also handles corresponding region projections of the place.
    #[tracing::instrument(skip(self, repacker, location, obtain_reason))]
    pub(crate) fn obtain(
        &mut self,
        repacker: CompilerCtxt<'_, 'tcx>,
        place: Place<'tcx>,
        capabilities: &mut PlaceCapabilities<'tcx>,
        location: Location,
        obtain_reason: ObtainReason,
    ) -> Result<ExecutedActions<'tcx>, PcgError> {
        let mut actions = ExecutedActions::new();
        if obtain_reason.min_post_obtain_capability() != CapabilityKind::Read {
            actions.extend(self.upgrade_closest_root_to_exclusive(
                place,
                capabilities,
                repacker,
            )?);
        }

        if !self.contains(place, repacker) {
            let extra_acts =
                self.expand_to(place, capabilities, repacker, obtain_reason, location)?;
            actions.extend(extra_acts);
        }
        if !place.is_owned(repacker) {
            pcg_validity_assert!(
                capabilities.get(place.into()).is_some(),
                "{:?}: Place {:?} does not have a capability after obtain {:?}",
                location,
                place,
                obtain_reason
            );
            pcg_validity_assert!(
                capabilities.get(place.into()).unwrap()
                    >= obtain_reason.min_post_obtain_capability(),
                "{:?} Capability {:?} for {:?} is not greater than {:?}",
                location,
                capabilities.get(place.into()).unwrap(),
                place,
                obtain_reason.min_post_obtain_capability()
            );
        }
        Ok(actions)
    }

    pub(crate) fn upgrade_closest_root_to_exclusive(
        &mut self,
        place: Place<'tcx>,
        capabilities: &mut PlaceCapabilities<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> Result<ExecutedActions<'tcx>, PcgError> {
        // It's possible that `place` is not in the PCG, `expand_root` is the leaf
        // node from which place will be expanded to.

        let mut expand_root = place;
        while capabilities.get(expand_root.into()).is_none() {
            if expand_root.is_owned(repacker) {
                return Ok(ExecutedActions::new());
            }
            expand_root = expand_root.parent_place().unwrap();
        }

        // The expand_root may have capability read only. We upgrade it to
        // Exclusive, then we change all Read permissions from `expand_root`'s
        // parents to be None instead to ensure they are no longer accessible.

        if !expand_root.is_owned(repacker)
            && capabilities.get(expand_root.into()) == Some(CapabilityKind::Read)
        {
            self.upgrade_read_to_exclusive(expand_root, capabilities, repacker)
        } else {
            Ok(ExecutedActions::new())
        }
    }

    pub(crate) fn upgrade_read_to_exclusive(
        &mut self,
        place: Place<'tcx>,
        capabilities: &mut PlaceCapabilities<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> Result<ExecutedActions<'tcx>, PcgError> {
        let mut actions = ExecutedActions::new();
        self.record_and_apply_action(
            BorrowPCGAction::restore_capability(place.into(), CapabilityKind::Exclusive),
            &mut actions,
            capabilities,
            repacker,
        )?;
        actions.extend(self.remove_read_permission_upwards(place, capabilities, repacker)?);
        Ok(actions)
    }

    pub(crate) fn remove_read_permission_upwards(
        &mut self,
        mut current: Place<'tcx>,
        capabilities: &mut PlaceCapabilities<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> Result<ExecutedActions<'tcx>, PcgError> {
        let mut actions = ExecutedActions::new();
        while !current.is_owned(repacker)
            && capabilities.get(current.into()) == Some(CapabilityKind::Read)
        {
            self.record_and_apply_action(
                BorrowPCGAction::weaken(current, CapabilityKind::Read, None),
                &mut actions,
                capabilities,
                repacker,
            )?;
            let parent = match current.parent_place() {
                Some(parent) => parent,
                None => break,
            };
            current = parent;
        }
        Ok(actions)
    }

    /// Inserts edges to ensure that the borrow PCG is expanded to at least
    /// `to_place`. We assume that any unblock operations have already been
    /// performed.
    fn expand_to(
        &mut self,
        to_place: Place<'tcx>,
        capabilities: &mut PlaceCapabilities<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
        obtain_reason: ObtainReason,
        location: Location,
    ) -> Result<ExecutedActions<'tcx>, PcgError> {
        tracing::debug!("Expanding to {:?}", to_place);
        let for_exclusive = obtain_reason.min_post_obtain_capability() != CapabilityKind::Read;
        let mut actions = ExecutedActions::new();

        for (base, _) in to_place.iter_projections(ctxt) {
            let base: Place<'tcx> = base;
            let base = base.with_inherent_region(ctxt);
            let expand_result = base.expand_one_level(to_place, ctxt)?;
            let expansion = expand_result.expansion();
            let target = expand_result.target_place;

            // We don't introduce an expansion if the place is owned, because
            // that is handled by the owned PCG.
            if !target.is_owned(ctxt) {
                let place_expansion = PlaceExpansion::from_places(expansion.clone(), ctxt);
                let expansion: BorrowPCGExpansion<'tcx, LocalNode<'tcx>> =
                    BorrowPCGExpansion::new(base.into(), place_expansion, location, ctxt)?;

                if expansion
                    .blocked_by_nodes(ctxt)
                    .iter()
                    .all(|node| self.contains(*node, ctxt))
                {
                    continue;
                }

                if base.is_mut_ref(ctxt) {
                    let place: MaybeOldPlace<'tcx> = base.into();
                    self.label_region_projection(
                        &place.base_region_projection(ctxt).unwrap(),
                        Some(location.into()),
                        ctxt,
                    );
                }

                let action = BorrowPCGAction::add_edge(
                    BorrowPCGEdge::new(
                        BorrowPCGEdgeKind::BorrowPCGExpansion(expansion),
                        PathConditions::new(location.block),
                    ),
                    for_exclusive,
                );
                self.record_and_apply_action(action, &mut actions, capabilities, ctxt)?;
            }

            for rp in base.region_projections(ctxt) {
                let dest_places = expansion
                    .iter()
                    .filter(|e| {
                        e.region_projections(ctxt)
                            .into_iter()
                            .any(|child_rp| rp.region(ctxt) == child_rp.region(ctxt))
                    })
                    .copied()
                    .collect::<Vec<_>>();
                if !dest_places.is_empty() {
                    let rp: RegionProjection<'tcx, MaybeOldPlace<'tcx>> = rp.into();
                    let place_expansion = PlaceExpansion::from_places(dest_places, ctxt);
                    let expansion =
                        BorrowPCGExpansion::new(rp.into(), place_expansion, location, ctxt)?;
                    self.record_and_apply_action(
                        BorrowPCGAction::add_edge(
                            BorrowPCGEdge::new(
                                BorrowPCGEdgeKind::BorrowPCGExpansion(expansion),
                                PathConditions::new(location.block),
                            ),
                            for_exclusive,
                        ),
                        &mut actions,
                        capabilities,
                        ctxt,
                    )?;
                    self.label_region_projection(&rp, Some(SnapshotLocation::before(location).into()), ctxt);
                }
            }
        }

        Ok(actions)
    }
}
