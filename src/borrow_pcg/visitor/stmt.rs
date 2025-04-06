use super::BorrowsVisitor;
use crate::{
    borrow_pcg::{
        action::{BorrowPCGAction, MakePlaceOldReason},
        borrow_pcg_edge::BorrowPCGEdge,
        edge::outlives::{BorrowFlowEdge, BorrowFlowEdgeKind},
        path_condition::PathConditions,
        region_projection::{MaybeRemoteRegionProjectionBase, RegionProjection},
        state::obtain::ObtainReason,
    },
    free_pcs::CapabilityKind,
    pcg::{EvalStmtPhase, PCGUnsupportedError, PcgError},
    pcg_validity_assert,
    rustc_interface::middle::{
        mir::{AggregateKind, BorrowKind, Location, Operand, Rvalue, Statement, StatementKind},
        ty::{self},
    },
    utils::{self, display::DisplayWithCompilerCtxt, maybe_old::MaybeOldPlace},
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
                self.apply_action(BorrowPCGAction::make_place_old(
                    place,
                    MakePlaceOldReason::StorageDead,
                ));
                let actions = self.state.pack_old_and_dead_leaves(
                    self.ctxt,
                    self.capabilities,
                    location,
                    self.bc.as_ref(),
                )?;
                self.record_actions(actions);
            }
            StatementKind::Assign(box (target, _)) => {
                let target: utils::Place<'tcx> = (*target).into();
                // Any references to target should be made old because it
                // will be overwritten in the assignment.
                if target.is_ref(self.ctxt)
                    && self.state.graph().contains(target, self.ctxt)
                {
                    self.apply_action(BorrowPCGAction::make_place_old(
                        (*target).into(),
                        MakePlaceOldReason::ReAssign,
                    ));

                    // The permission to the target may have been Read originally.
                    // Now, because it's been made old, the non-old place should be a leaf,
                    // and its permission should be Exclusive.
                    if self.capabilities.get(target.into()) == Some(CapabilityKind::Read) {
                        self.state.apply_action(
                            BorrowPCGAction::restore_capability(
                                target.into(),
                                CapabilityKind::Exclusive,
                            ),
                            self.capabilities,
                            self.ctxt,
                        )?;
                    }
                }
                let obtain_reason = ObtainReason::AssignTarget;
                let obtain_actions = self.state.obtain(
                    self.ctxt,
                    target,
                    self.capabilities,
                    location,
                    obtain_reason,
                )?;
                self.record_actions(obtain_actions);

                if !target.is_owned(self.ctxt) {
                    if let Some(target_cap) = self.capabilities.get(target.into()) {
                        if target_cap != CapabilityKind::Write {
                            pcg_validity_assert!(
                                target_cap >= CapabilityKind::Write,
                                "{:?}: {} cap {:?} is not greater than {:?}",
                                location,
                                target.to_short_string(self.ctxt),
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
                        panic!(
                            "No capability found for {}",
                            target.to_short_string(self.ctxt)
                        );
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
        assert!(self.phase == EvalStmtPhase::PostMain);
        if let StatementKind::Assign(box (target, rvalue)) = &statement.kind {
            let target: utils::Place<'tcx> = (*target).into();
            self.apply_action(BorrowPCGAction::set_latest(
                target,
                location,
                "Target of Assignment",
            ));
            if !target.is_owned(self.ctxt) {
                self.capabilities
                    .insert(target.into(), CapabilityKind::Exclusive);
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
                            .region_projections(self.ctxt)
                            .iter()
                            .enumerate()
                        {
                            let source_proj = source_proj.with_base(
                                MaybeOldPlace::new(
                                    source_proj.base,
                                    Some(self.state.get_latest(source_proj.base)),
                                ),
                                self.ctxt,
                            );
                            self.connect_outliving_projections(
                                source_proj,
                                target,
                                location,
                                |_| BorrowFlowEdgeKind::Aggregate {
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
                            target.ty(self.ctxt).ty.kind()
                        {
                            self.apply_action(BorrowPCGAction::add_edge(
                                BorrowPCGEdge::new(
                                    BorrowFlowEdge::new(
                                        RegionProjection::new(
                                            (*const_region).into(),
                                            MaybeRemoteRegionProjectionBase::Const(c.const_),
                                            None,
                                            self.ctxt,
                                        )
                                        .unwrap(),
                                        RegionProjection::new(
                                            (*target_region).into(),
                                            target,
                                            None,
                                            self.ctxt,
                                        )
                                        .unwrap()
                                        .into(),
                                        BorrowFlowEdgeKind::ConstRef,
                                        self.ctxt,
                                    )
                                    .into(),
                                    PathConditions::AtBlock(location.block),
                                ),
                                true,
                            ));
                        }
                    }
                }
                Rvalue::Use(operand @ (Operand::Move(from) | Operand::Copy(from))) => {
                    let from: utils::Place<'tcx> = (*from).into();
                    let (from, kind) = if matches!(operand, Operand::Move(_)) {
                        (
                            MaybeOldPlace::new(from, Some(self.state.get_latest(from))),
                            BorrowFlowEdgeKind::Move,
                        )
                    } else {
                        (from.into(), BorrowFlowEdgeKind::CopySharedRef)
                    };
                    for source_proj in from.region_projections(self.ctxt).into_iter() {
                        self.connect_outliving_projections(source_proj, target, location, |_| kind);
                    }
                }
                Rvalue::Ref(region, kind, blocked_place) => {
                    let blocked_place: utils::Place<'tcx> = (*blocked_place).into();
                    let blocked_place = blocked_place.with_inherent_region(self.ctxt);
                    if !target.ty(self.ctxt).ty.is_ref() {
                        return Err(PcgError::unsupported(
                            PCGUnsupportedError::AssignBorrowToNonReferenceType,
                        ));
                    }
                    if matches!(kind, BorrowKind::Fake(_)) {
                        return Ok(());
                    }
                    self.state.add_borrow(
                        blocked_place.into(),
                        target,
                        *kind,
                        location,
                        *region,
                        self.capabilities,
                        self.ctxt,
                    );
                    let target_region = target.ty_region(self.ctxt).unwrap();
                    for source_proj in blocked_place.region_projections(self.ctxt).into_iter() {
                        self.connect_outliving_projections(
                            source_proj.into(),
                            target,
                            location,
                            |region| BorrowFlowEdgeKind::BorrowOutlives {
                                toplevel: region == target_region,
                            },
                        );
                        if kind.mutability().is_mut() {
                            self.state.label_region_projection(
                                &source_proj.into(),
                                location.into(),
                                self.ctxt,
                            );
                        }
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }
}
