use super::PcgVisitor;
use crate::action::BorrowPcgAction;
use crate::borrow_pcg::borrow_pcg_edge::BorrowPcgEdge;
use crate::borrow_pcg::edge::outlives::{BorrowFlowEdge, BorrowFlowEdgeKind};
use crate::borrow_pcg::has_pcs_elem::LabelLifetimeProjectionPredicate;
use crate::borrow_pcg::region_projection::{LifetimeProjection, MaybeRemoteRegionProjectionBase};
use crate::pcg::CapabilityKind;
use crate::pcg::EvalStmtPhase;
use crate::pcg::obtain::{ActionApplier, HasSnapshotLocation, PlaceExpander};
use crate::pcg::place_capabilities::PlaceCapabilitiesInterface;
use crate::rustc_interface::middle::mir::{self, Operand, Rvalue};

use crate::rustc_interface::middle::ty::{self};
use crate::utils::maybe_old::MaybeLabelledPlace;
use crate::utils::{self, AnalysisLocation, DataflowCtxt, SnapshotLocation};

use super::{PcgError, PcgUnsupportedError};

impl<'a, 'tcx: 'a, Ctxt: DataflowCtxt<'a, 'tcx>> PcgVisitor<'_, 'a, 'tcx, Ctxt> {
    // The label that should be used when referencing (after PostOperands), the
    // value at the place before the move.
    pub(crate) fn pre_operand_move_label(&self) -> SnapshotLocation {
        SnapshotLocation::Before(AnalysisLocation::new(
            self.location(),
            EvalStmtPhase::PostOperands,
        ))
    }

    // Returns the maybe-labelled place to use to reference the value of an
    // operand after the PostOperands phase. If the operand was copied, the
    // place is returned as-is. If the operand was moved, the place is returned
    // with the label of the value before the move.
    // Returns `None` if the operand is a constant.
    pub(crate) fn maybe_labelled_operand_place(
        &self,
        operand: &Operand<'tcx>,
    ) -> Option<MaybeLabelledPlace<'tcx>> {
        match operand {
            Operand::Copy(place) => Some((*place).into()),
            Operand::Move(place) => Some(MaybeLabelledPlace::new(
                (*place).into(),
                Some(self.pre_operand_move_label()),
            )),
            Operand::Constant(_) => None,
        }
    }

    pub(crate) fn assign_post_main(
        &mut self,
        target: utils::Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
    ) -> Result<(), PcgError> {
        let ctxt = self.ctxt;

        // If `target` is a reference, then the dereferenced place technically
        // still retains its capabilities. However, because we currently only
        // keep capabilities for non-labelled places, we remove all the capabilities
        // to everything postfix of `target`.
        //
        // We should change this logic once we start keeping capabilities for
        // labelled places.
        if target.is_ref(ctxt) {
            self.pcg.capabilities.remove_all_postfixes(target, ctxt);
        }

        self.pcg
            .capabilities
            .insert(target, CapabilityKind::Exclusive, self.ctxt);
        match rvalue {
            Rvalue::Aggregate(
                box (mir::AggregateKind::Adt(..)
                | mir::AggregateKind::Tuple
                | mir::AggregateKind::Array(..)),
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
                        .lifetime_projections(self.ctxt)
                        .iter()
                        .enumerate()
                    {
                        let maybe_labelled = self.maybe_labelled_operand_place(field).unwrap();
                        let source_proj = source_proj.with_base(maybe_labelled);
                        self.connect_outliving_projections(source_proj, target, |_| {
                            BorrowFlowEdgeKind::Aggregate {
                                field_idx,
                                target_rp_index: source_rp_idx,
                            }
                        })?;
                    }
                }
            }
            Rvalue::Use(Operand::Constant(box c)) => {
                if let ty::TyKind::Ref(const_region, _, _) = c.ty().kind()
                    && let ty::TyKind::Ref(target_region, _, _) = target.ty(self.ctxt).ty.kind()
                {
                    self.record_and_apply_action(
                        BorrowPcgAction::add_edge(
                            BorrowPcgEdge::new(
                                BorrowFlowEdge::new(
                                    LifetimeProjection::new(
                                        (*const_region).into(),
                                        MaybeRemoteRegionProjectionBase::Const(c.const_),
                                        None,
                                        self.ctxt,
                                    )
                                    .unwrap(),
                                    LifetimeProjection::new(
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
                                self.pcg.borrow.validity_conditions.clone(),
                            ),
                            "assign_post_main",
                            self.ctxt,
                        )
                        .into(),
                    )?;
                }
            }
            Rvalue::Use(operand @ (Operand::Move(from) | Operand::Copy(from)))
            | Rvalue::Cast(_, operand @ (Operand::Move(from) | Operand::Copy(from)), _) => {
                let from: utils::Place<'tcx> = (*from).into();
                let (from, kind) = if matches!(operand, Operand::Move(_)) {
                    (
                        MaybeLabelledPlace::new(from, Some(self.pre_operand_move_label())),
                        BorrowFlowEdgeKind::Move,
                    )
                } else {
                    (from.into(), BorrowFlowEdgeKind::CopyRef)
                };
                for (source_proj, target_proj) in from
                    .lifetime_projections(self.ctxt)
                    .into_iter()
                    .zip(target.lifetime_projections(self.ctxt).into_iter())
                {
                    self.record_and_apply_action(
                        BorrowPcgAction::add_edge(
                            BorrowPcgEdge::new(
                                BorrowFlowEdge::new(
                                    source_proj.into(),
                                    target_proj.into(),
                                    kind,
                                    self.ctxt,
                                )
                                .into(),
                                self.pcg.borrow.validity_conditions.clone(),
                            ),
                            "assign_post_main",
                            self.ctxt,
                        )
                        .into(),
                    )?;
                    // Redirect all future edges from `from` to now be from `target`
                    self.place_obtainer().redirect_source_of_future_edges(
                        source_proj,
                        target_proj.into(),
                        ctxt,
                    )?;
                }
            }
            Rvalue::Ref(borrow_region, kind, blocked_place) => {
                let blocked_place: utils::Place<'tcx> = (*blocked_place).into();
                let blocked_place = blocked_place.with_inherent_region(self.ctxt);
                if !target.ty(self.ctxt).ty.is_ref() {
                    return Err(PcgError::unsupported(
                        PcgUnsupportedError::AssignBorrowToNonReferenceType,
                    ));
                }
                if matches!(kind, mir::BorrowKind::Fake(_)) {
                    return Ok(());
                }
                self.pcg.borrow.add_borrow(
                    blocked_place,
                    target,
                    *kind,
                    self.location(),
                    *borrow_region,
                    &mut self.pcg.capabilities,
                    self.ctxt,
                );
                self.label_lifetime_projections_for_borrow(blocked_place, target, *kind)?;
            }
            _ => {}
        }
        Ok(())
    }

    fn label_lifetime_projections_for_borrow(
        &mut self,
        blocked_place: utils::Place<'tcx>,
        target: utils::Place<'tcx>,
        kind: mir::BorrowKind,
    ) -> Result<(), PcgError> {
        let ctxt = self.ctxt;
        for source_proj in blocked_place.lifetime_projections(self.ctxt).into_iter() {
            let mut obtainer = self.place_obtainer();
            let source_proj = if kind.mutability().is_mut() {
                let label = obtainer.prev_snapshot_location();
                obtainer.apply_action(
                    BorrowPcgAction::label_lifetime_projection(
                        LabelLifetimeProjectionPredicate::Postfix(source_proj.into()),
                        Some(label.into()),
                        "Label region projections of newly borrowed place",
                    )
                    .into(),
                )?;
                source_proj.with_label(Some(label.into()), self.ctxt)
            } else {
                source_proj.with_label(
                    obtainer
                        .label_for_shared_expansion_of_rp(source_proj, obtainer.ctxt)
                        .map(|l| l.into()),
                    self.ctxt,
                )
            };
            let source_region = source_proj.region(self.ctxt);
            let mut nested_ref_mut_targets = vec![];
            for target_proj in target.lifetime_projections(self.ctxt).into_iter() {
                let target_region = target_proj.region(self.ctxt);
                if self
                    .ctxt
                    .bc()
                    .outlives(source_region, target_region, self.location())
                {
                    let regions_equal =
                        self.ctxt
                            .bc()
                            .same_region(source_region, target_region, self.location());
                    self.record_and_apply_action(
                        BorrowPcgAction::add_edge(
                            BorrowPcgEdge::new(
                                BorrowFlowEdge::new(
                                    source_proj.into(),
                                    target_proj.into(),
                                    BorrowFlowEdgeKind::BorrowOutlives { regions_equal },
                                    self.ctxt,
                                )
                                .into(),
                                self.pcg.borrow.validity_conditions.clone(),
                            ),
                            "assign_post_main",
                            self.ctxt,
                        )
                        .into(),
                    )?;
                    if regions_equal && kind.mutability().is_mut() {
                        nested_ref_mut_targets.push(target_proj.into());
                    }
                }
            }
            self.place_obtainer().add_and_update_placeholder_edges(
                source_proj.into(),
                &nested_ref_mut_targets,
                "assign",
                ctxt,
            )?;
        }
        Ok(())
    }
}
