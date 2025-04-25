use super::BorrowsVisitor;
use crate::{
    borrow_pcg::{
        action::{BorrowPCGAction, MakePlaceOldReason},
        borrow_pcg_edge::{BorrowPCGEdge, BorrowPCGEdgeLike},
        edge::{
            kind::BorrowPCGEdgeKind,
            outlives::{BorrowFlowEdge, BorrowFlowEdgeKind},
        },
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
                let actions =
                    self.state
                        .pack_old_and_dead_leaves(self.ctxt, self.capabilities, location)?;
                self.record_actions(actions);
            }
            StatementKind::Assign(box (target, _)) => {
                let target: utils::Place<'tcx> = (*target).into();
                // Any references to target should be made old because it
                // will be overwritten in the assignment.
                if target.is_ref(self.ctxt) && self.state.graph().contains(target, self.ctxt) {
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
                        pcg_validity_assert!(
                            false,
                            "No capability found for {}",
                            target.to_short_string(self.ctxt)
                        );
                    }
                }
                for rp in target.region_projections(self.ctxt).into_iter() {
                    let blocked_edges = self
                        .state
                        .graph()
                        .edges_blocked_by(rp.into(), self.ctxt)
                        .map(|edge| edge.to_owned_edge())
                        .collect::<Vec<_>>();
                    for edge in blocked_edges {
                        let should_remove =
                            !matches!(edge.kind(), BorrowPCGEdgeKind::BorrowPCGExpansion(_));
                        if should_remove {
                            let actions = self.state.remove_edge_and_set_latest(
                                edge,
                                self.capabilities,
                                location,
                                self.ctxt,
                                "Assign",
                            )?;
                            self.record_actions(actions);
                        }
                    }
                }
            }
            _ => {}
        }
        Ok(())
    }

    fn assign_post_main(
        &mut self,
        target: utils::Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
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
                        self.connect_outliving_projections(source_proj, target, location, |_| {
                            BorrowFlowEdgeKind::Aggregate {
                                field_idx,
                                target_rp_index: source_rp_idx,
                            }
                        });
                    }
                }
            }
            Rvalue::Use(Operand::Constant(box c)) => {
                if let ty::TyKind::Ref(const_region, _, _) = c.ty().kind() {
                    if let ty::TyKind::Ref(target_region, _, _) = target.ty(self.ctxt).ty.kind() {
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
                for (source_proj, target_proj) in from
                    .region_projections(self.ctxt)
                    .into_iter()
                    .zip(target.region_projections(self.ctxt).into_iter())
                {
                    self.apply_action(BorrowPCGAction::add_edge(
                        BorrowPCGEdge::new(
                            BorrowFlowEdge::new(
                                source_proj.into(),
                                target_proj.into(),
                                kind,
                                self.ctxt,
                            )
                            .into(),
                            PathConditions::AtBlock(location.block),
                        ),
                        true,
                    ));
                }
            }
            Rvalue::Ref(borrow_region, kind, blocked_place) => {
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
                    *borrow_region,
                    self.capabilities,
                    self.ctxt,
                );
                for mut source_proj in blocked_place.region_projections(self.ctxt).into_iter() {
                    let source_proj = if kind.mutability().is_mut() {
                        self.state.label_region_projection(
                            &source_proj.into(),
                            Some(location.into()),
                            self.ctxt,
                        );
                        source_proj.label = Some(location.into());
                        source_proj
                    } else {
                        source_proj
                    };
                    let source_region = source_proj.region(self.ctxt);
                    for target_proj in target.region_projections(self.ctxt).into_iter() {
                        let target_region = target_proj.region(self.ctxt);
                        if self.ctxt.bc.outlives(source_region, target_region) {
                            let regions_equal =
                                self.ctxt.bc.same_region(source_region, target_region);
                            self.apply_action(BorrowPCGAction::add_edge(
                                BorrowPCGEdge::new(
                                    BorrowFlowEdge::new(
                                        source_proj.into(),
                                        target_proj.into(),
                                        BorrowFlowEdgeKind::BorrowOutlives { regions_equal },
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
            self.assign_post_main((*target).into(), rvalue, location)?;
        }
        Ok(())
    }
}
