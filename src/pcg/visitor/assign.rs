use super::PcgVisitor;
use crate::action::BorrowPcgAction;
use crate::borrow_pcg::borrow_pcg_edge::BorrowPcgEdge;
use crate::borrow_pcg::edge::kind::BorrowPcgEdgeKind;
use crate::borrow_pcg::edge::outlives::{BorrowFlowEdge, BorrowFlowEdgeKind};
use crate::borrow_pcg::has_pcs_elem::LabelRegionProjectionPredicate;
use crate::borrow_pcg::region_projection::{MaybeRemoteRegionProjectionBase, RegionProjection};
use crate::free_pcs::CapabilityKind;
use crate::pcg::obtain::PlaceExpander;
use crate::pcg::place_capabilities::PlaceCapabilitiesInterface;
use crate::rustc_interface::middle::mir::{self, Operand, Rvalue};

use crate::rustc_interface::middle::ty::{self};
use crate::utils::display::DisplayWithCompilerCtxt;
use crate::utils::maybe_old::MaybeOldPlace;
use crate::utils::{self, Place, SnapshotLocation};

use super::{PcgError, PcgUnsupportedError};

impl<'tcx> PcgVisitor<'_, '_, 'tcx> {
    pub(crate) fn assign_post_main(
        &mut self,
        target: utils::Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
    ) -> Result<(), PcgError> {
        let mut ctxt = self.ctxt;
        self.record_and_apply_action(
            BorrowPcgAction::set_latest(
                target,
                SnapshotLocation::After(self.location),
                "Target of Assignment",
            )
            .into(),
        )?;
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
                        .region_projections(self.ctxt)
                        .iter()
                        .enumerate()
                    {
                        let source_proj = source_proj.with_base(MaybeOldPlace::new(
                            source_proj.base,
                            Some(self.pcg.borrow.get_latest(source_proj.base, self.ctxt)),
                        ));
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
                                self.pcg.borrow.path_conditions.clone(),
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
                        MaybeOldPlace::new(from, Some(self.pcg.borrow.get_latest(from, self.ctxt))),
                        BorrowFlowEdgeKind::Move,
                    )
                } else {
                    (from.into(), BorrowFlowEdgeKind::CopyRef)
                };
                for (source_proj, target_proj) in from
                    .region_projections(self.ctxt)
                    .into_iter()
                    .zip(target.region_projections(self.ctxt).into_iter())
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
                                self.pcg.borrow.path_conditions.clone(),
                            ),
                            "assign_post_main",
                            self.ctxt,
                        )
                        .into(),
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
                    self.location,
                    *borrow_region,
                    &mut self.pcg.capabilities,
                    self.ctxt,
                );
                for source_proj in blocked_place.region_projections(self.ctxt).into_iter() {
                    let mut obtainer = self.place_obtainer();
                    let source_proj = if kind.mutability().is_mut() {
                        let label = obtainer.current_snapshot_location();
                        obtainer.apply_action(
                            BorrowPcgAction::label_region_projection(
                                LabelRegionProjectionPredicate::Postfix(source_proj.into()),
                                Some(label.into()),
                                "Label region projections of newly borrowed place",
                            )
                            .into(),
                        )?;
                        source_proj.with_label(Some(label.into()), self.ctxt)
                    } else {
                        source_proj.with_label(
                            obtainer.label_for_shared_expansion_of_rp(source_proj, obtainer.ctxt),
                            self.ctxt,
                        )
                    };
                    let source_region = source_proj.region(self.ctxt);
                    let mut nested_ref_mut_targets = vec![];
                    for target_proj in target.region_projections(self.ctxt).into_iter() {
                        let target_region = target_proj.region(self.ctxt);
                        if self.ctxt.bc.outlives(source_region, target_region) {
                            let regions_equal =
                                self.ctxt.bc.same_region(source_region, target_region);
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
                                        self.pcg.borrow.path_conditions.clone(),
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
            }
            _ => {}
        }
        Ok(())
    }
}
