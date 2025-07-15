use super::PcgVisitor;

use crate::action::BorrowPcgAction;
use crate::borrow_pcg::action::MakePlaceOldReason;
use crate::borrow_pcg::borrow_pcg_edge::BorrowPcgEdgeLike;
use crate::borrow_pcg::edge::kind::BorrowPcgEdgeKind;
use crate::borrow_pcg::edge_data::LabelPlacePredicate;
use crate::free_pcs::CapabilityKind;
use crate::pcg::place_capabilities::PlaceCapabilitiesInterface;
use crate::rustc_interface::middle::mir::{Statement, StatementKind};

use crate::utils::visitor::FallableVisitor;
use crate::utils::{self};

use super::{EvalStmtPhase, PcgError};

impl<'tcx> PcgVisitor<'_, '_, 'tcx> {
    pub(crate) fn perform_statement_actions(
        &mut self,
        statement: &Statement<'tcx>,
    ) -> Result<(), PcgError> {
        self.super_statement_fallable(statement, self.location)?;
        match self.phase {
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
        assert!(self.phase == EvalStmtPhase::PreMain);
        match &statement.kind {
            StatementKind::StorageDead(local) => {
                let place: utils::Place<'tcx> = (*local).into();
                self.record_and_apply_action(
                    BorrowPcgAction::make_place_old(
                        LabelPlacePredicate::PrefixWithoutIndirectionOrPostfix(place),
                        MakePlaceOldReason::StorageDead,
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
                    if self.pcg.capabilities.get(target) == Some(CapabilityKind::Read) {
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

                if !target.is_owned(self.ctxt) {
                    if let Some(target_cap) = self.pcg.capabilities.get(target) {
                        if target_cap != CapabilityKind::Write {
                            self.record_and_apply_action(
                                BorrowPcgAction::weaken(
                                    target,
                                    target_cap,
                                    Some(CapabilityKind::Write),
                                    "pre_main"
                                )
                                .into(),
                            )?;
                        }
                    } else {
                        // TODO: This is failing in code that loops for some reason
                        // pcg_validity_assert!(
                        //     false,
                        //     "No capability found for {} in {:?}",
                        //     target.to_short_string(self.ctxt),
                        //     statement,
                        // );
                    }
                }
                for rp in target.region_projections(self.ctxt).into_iter() {
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
                            self.remove_edge_and_perform_associated_state_updates(
                                edge, false, "Assign",
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
        assert!(self.phase == EvalStmtPhase::PostMain);
        if let StatementKind::Assign(box (target, rvalue)) = &statement.kind {
            self.assign_post_main((*target).into(), rvalue)?;
        }
        Ok(())
    }
}
