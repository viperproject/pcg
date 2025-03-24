use super::BorrowsVisitor;
use crate::{
    borrow_pcg::{
        action::BorrowPCGAction,
        borrow_pcg_edge::BorrowPCGEdge,
        edge::outlives::{OutlivesEdge, OutlivesEdgeKind},
        path_condition::PathConditions,
        region_projection::{MaybeRemoteRegionProjectionBase, RegionProjection},
        state::obtain::ObtainReason,
        visitor::StatementStage,
    },
    combined_pcs::{EvalStmtPhase, PCGUnsupportedError, PcgError},
    free_pcs::CapabilityKind,
    pcg_validity_assert,
    rustc_interface::middle::{
        mir::{AggregateKind, BorrowKind, Location, Operand, Rvalue, Statement, StatementKind},
        ty::{self},
    },
    utils::{self, display::DisplayWithRepacker, maybe_old::MaybeOldPlace},
};

impl<'tcx> BorrowsVisitor<'tcx, '_, '_> {
    pub(crate) fn stmt_pre_main(
        &mut self,
        statement: &Statement<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        match &statement.kind {
            StatementKind::StorageDead(local) => {
                let place: utils::Place<'tcx> = (*local).into();
                self.apply_action(BorrowPCGAction::make_place_old(place));
                let actions = self
                    .domain
                    .data
                    .get_mut(EvalStmtPhase::PostMain)
                    .pack_old_and_dead_leaves(self.repacker, location, self.domain.bc.as_ref())?;
                self.record_actions(actions);
            }
            StatementKind::Assign(box (target, _)) => {
                let target: utils::Place<'tcx> = (*target).into();
                // Any references to target should be made old because it
                // will be overwritten in the assignment.
                if target.is_ref(self.repacker)
                    && self
                        .domain
                        .post_main_state()
                        .graph()
                        .contains(target, self.repacker)
                {
                    self.apply_action(BorrowPCGAction::make_place_old((*target).into()));

                    // The permission to the target may have been Read originally.
                    // Now, because it's been made old, the non-old place should be a leaf,
                    // and its permission should be Exclusive.
                    if self.domain.post_state_mut().get_capability(target.into())
                        == Some(CapabilityKind::Read)
                    {
                        self.domain.post_state_mut().apply_action(
                            BorrowPCGAction::restore_capability(
                                target.into(),
                                CapabilityKind::Exclusive,
                            ),
                            self.repacker,
                        )?;
                    }
                }
                let obtain_reason = ObtainReason::AssignTarget;
                let obtain_actions = self.domain.post_state_mut().obtain(
                    self.repacker,
                    target,
                    location,
                    obtain_reason,
                )?;
                self.record_actions(obtain_actions);

                if !target.is_owned(self.repacker) {
                    if let Some(target_cap) =
                        self.domain.post_state_mut().get_capability(target.into())
                    {
                        if target_cap != CapabilityKind::Write {
                            pcg_validity_assert!(
                                target_cap >= CapabilityKind::Write,
                                "{:?}: {} cap {:?} is not greater than {:?}",
                                location,
                                target.to_short_string(self.repacker),
                                target_cap,
                                CapabilityKind::Write
                            );
                            self.apply_action(BorrowPCGAction::weaken(
                                target,
                                target_cap,
                                Some(CapabilityKind::Write),
                            ));
                        }
                    } else {
                        // TODO
                        // panic!(
                        //     "No capability found for {}",
                        //     target.to_short_string(self.repacker)
                        // );
                    }
                }
            }
            _ => {}
        }
        Ok(())
    }
    pub(crate) fn stmt_post_main(
        &mut self,
        statement: &Statement<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        assert!(!self.preparing);
        assert!(self.stage == StatementStage::Main);
        if let StatementKind::Assign(box (target, rvalue)) = &statement.kind {
            let target: utils::Place<'tcx> = (*target).into();
            self.apply_action(BorrowPCGAction::set_latest(
                target,
                location,
                "Target of Assignment",
            ));
            let state = self.domain.post_state_mut();
            if !target.is_owned(self.repacker) {
                state.set_capability(target.into(), CapabilityKind::Exclusive, self.repacker);
            }
            match rvalue {
                Rvalue::Aggregate(
                    box (AggregateKind::Adt(..) | AggregateKind::Tuple | AggregateKind::Array(..)),
                    fields,
                ) => {
                    let target: utils::Place<'tcx> = (*target).into();
                    for (field_idx, field) in fields.iter().enumerate() {
                        let operand_place: utils::Place<'tcx> = if let Some(place) = field.place() {
                            place.into()
                        } else {
                            continue;
                        };
                        for (source_rp_idx, source_proj) in operand_place
                            .region_projections(self.repacker)
                            .iter()
                            .enumerate()
                        {
                            let source_proj = source_proj.with_base(
                                MaybeOldPlace::new(
                                    source_proj.base,
                                    Some(
                                        self.domain.post_main_state().get_latest(source_proj.base),
                                    ),
                                ),
                                self.repacker,
                            );
                            self.connect_outliving_projections(
                                source_proj,
                                target,
                                location,
                                |_| OutlivesEdgeKind::Aggregate {
                                    field_idx,
                                    target_rp_index: source_rp_idx,
                                },
                            );
                        }
                    }
                }
                Rvalue::Use(Operand::Constant(box c)) => {
                    if let ty::TyKind::Ref(const_region, _, _) = c.ty().kind() {
                        if let ty::TyKind::Ref(target_region, _, _) =
                            target.ty(self.repacker).ty.kind()
                        {
                            self.apply_action(BorrowPCGAction::add_edge(
                                BorrowPCGEdge::new(
                                    OutlivesEdge::new(
                                        RegionProjection::new(
                                            (*const_region).into(),
                                            MaybeRemoteRegionProjectionBase::Const(c.const_),
                                            self.repacker,
                                        )
                                        .unwrap(),
                                        RegionProjection::new(
                                            (*target_region).into(),
                                            target,
                                            self.repacker,
                                        )
                                        .unwrap()
                                        .into(),
                                        OutlivesEdgeKind::ConstRef,
                                        self.repacker,
                                    )
                                    .into(),
                                    PathConditions::AtBlock(location.block),
                                ),
                                true,
                            ));
                        }
                    }
                }
                Rvalue::Use(Operand::Move(from)) => {
                    let from: utils::Place<'tcx> = (*from).into();
                    let target: utils::Place<'tcx> = (*target).into();
                    let old_place = MaybeOldPlace::new(from, Some(state.get_latest(from)));
                    self.apply_action(BorrowPCGAction::rename_place(old_place, target.into()));
                }
                Rvalue::Use(Operand::Copy(from)) => {
                    let from_place: utils::Place<'tcx> = (*from).into();
                    for source_proj in from_place.region_projections(self.repacker).into_iter() {
                        self.connect_outliving_projections(
                            source_proj.into(),
                            target,
                            location,
                            |_| OutlivesEdgeKind::CopySharedRef,
                        );
                    }
                }
                Rvalue::Ref(region, kind, blocked_place) => {
                    let blocked_place: utils::Place<'tcx> = (*blocked_place).into();
                    let blocked_place = blocked_place.with_inherent_region(self.repacker);
                    if !target.ty(self.repacker).ty.is_ref() {
                        return Err(PcgError::unsupported(
                            PCGUnsupportedError::AssignBorrowToNonReferenceType,
                        ));
                    }
                    if matches!(kind, BorrowKind::Fake(_)) {
                        return Ok(());
                    }
                    state.add_borrow(
                        blocked_place.into(),
                        target,
                        *kind,
                        location,
                        *region,
                        self.repacker,
                    );
                    let target_region = target.ty_region(self.repacker).unwrap();
                    for source_proj in blocked_place.region_projections(self.repacker).into_iter() {
                        self.connect_outliving_projections(
                            source_proj.into(),
                            target,
                            location,
                            |region| OutlivesEdgeKind::BorrowOutlives {
                                toplevel: region == target_region,
                            },
                        );
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }
}
