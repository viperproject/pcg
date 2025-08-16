use super::PcgVisitor;

use crate::action::BorrowPcgAction;
use crate::borrow_pcg::action::LabelPlaceReason;
use crate::borrow_pcg::borrow_pcg_edge::BorrowPcgEdgeLike;
use crate::borrow_pcg::edge::kind::BorrowPcgEdgeKind;
use crate::pcg::CapabilityKind;
use crate::pcg::place_capabilities::PlaceCapabilitiesReader;
use crate::pcg_validity_assert;
use crate::rustc_interface::middle::mir::{Statement, StatementKind};

use crate::utils::visitor::FallableVisitor;
use crate::utils::{self, DataflowCtxt};

use super::{EvalStmtPhase, PcgError};

impl<'a, 'tcx: 'a, Ctxt: DataflowCtxt<'a, 'tcx>> PcgVisitor<'_, 'a, 'tcx, Ctxt> {
    pub(crate) fn perform_statement_actions(
        &mut self,
        statement: &Statement<'tcx>,
    ) -> Result<(), PcgError> {
        self.super_statement_fallable(statement, self.location())?;
        match self.phase() {
            EvalStmtPhase::PreMain => {
                self.stmt_pre_main(statement)?;
            }
            EvalStmtPhase::PostMain => {
                self.stmt_post_main(statement)?;
            }
            _ => {}
        }
        Ok(())
    }

    fn stmt_pre_main(&mut self, statement: &Statement<'tcx>) -> Result<(), PcgError> {
        assert!(self.phase() == EvalStmtPhase::PreMain);
        match &statement.kind {
            StatementKind::StorageDead(local) => {
                let place: utils::Place<'tcx> = (*local).into();
                let snapshot_location = self.prev_snapshot_location();
                self.record_and_apply_action(
                    BorrowPcgAction::label_place_and_update_related_capabilities(
                        place,
                        snapshot_location,
                        LabelPlaceReason::StorageDead,
                    )
                    .into(),
                )?;
            }
            StatementKind::Assign(box (target, _)) => {
                let target: utils::Place<'tcx> = (*target).into();
                // Any references to target should be made old because it
                // will be overwritten in the assignment.
                if target.is_ref(self.ctxt) && self.pcg.borrow.graph().contains(target, self.ctxt) {
                    // The permission to the target may have been Read originally.
                    // Now, because it's been made old, the non-old place should be a leaf,
                    // and its permission should be Exclusive.
                    if self
                        .pcg
                        .capabilities
                        .get(target, self.ctxt)
                        .map(|c| c.expect_concrete())
                        == Some(CapabilityKind::Read)
                    {
                        self.record_and_apply_action(
                            BorrowPcgAction::restore_capability(
                                target,
                                CapabilityKind::Exclusive,
                                "Assign: restore capability to exclusive",
                            )
                            .into(),
                        )?;
                    }
                }

                if let Some(target_cap_sym) = self.pcg.capabilities.get(target, self.ctxt) {
                    let target_cap = target_cap_sym.expect_concrete();
                    pcg_validity_assert!(
                        target_cap >= CapabilityKind::Write,
                        "target_cap: {:?}",
                        target_cap
                    );
                    if target_cap != CapabilityKind::Write {
                        self.record_and_apply_action(
                            BorrowPcgAction::weaken(
                                target,
                                target_cap,
                                Some(CapabilityKind::Write),
                                "pre_main",
                                self.ctxt,
                            )
                            .into(),
                        )?;
                    }
                }
                for rp in target.lifetime_projections(self.ctxt).into_iter() {
                    let blocked_edges = self
                        .pcg
                        .borrow
                        .graph()
                        .edges_blocked_by(rp.into(), self.ctxt)
                        .map(|edge| edge.to_owned_edge())
                        .collect::<Vec<_>>();
                    for edge in blocked_edges {
                        let should_remove =
                            !matches!(edge.kind(), BorrowPcgEdgeKind::BorrowPcgExpansion(_));
                        if should_remove {
                            self.place_obtainer()
                                .remove_edge_and_perform_associated_state_updates(
                                    &edge, "Assign",
                                )?;
                        }
                    }
                }
            }
            _ => {}
        }
        Ok(())
    }

    fn stmt_post_main(&mut self, statement: &Statement<'tcx>) -> Result<(), PcgError> {
        assert!(self.phase() == EvalStmtPhase::PostMain);
        if let StatementKind::Assign(box (target, rvalue)) = &statement.kind {
            self.assign_post_main((*target).into(), rvalue)?;
        }
        Ok(())
    }
}
