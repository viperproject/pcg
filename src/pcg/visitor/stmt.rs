use super::PcgVisitor;

use crate::borrow_pcg::action::{BorrowPCGAction, MakePlaceOldReason};
use crate::borrow_pcg::borrow_pcg_edge::BorrowPcgEdgeLike;
use crate::borrow_pcg::edge::kind::BorrowPcgEdgeKind;
use crate::free_pcs::CapabilityKind;
use crate::pcg_validity_assert;
use crate::rustc_interface::middle::mir::{Location, Statement, StatementKind};

use crate::utils::visitor::FallableVisitor;
use crate::utils::{self};

use super::{EvalStmtPhase, PcgError};

impl<'tcx> PcgVisitor<'_, '_, 'tcx> {
    pub(crate) fn perform_statement_actions(
        &mut self,
        statement: &Statement<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        self.super_statement_fallable(statement, location)?;
        match self.phase {
            EvalStmtPhase::PreMain => {
                match &statement.kind {
                    StatementKind::StorageDead(local) => {
                        let place: utils::Place<'tcx> = (*local).into();
                        self.record_and_apply_action(
                            BorrowPCGAction::make_place_old(place, MakePlaceOldReason::StorageDead)
                                .into(),
                        )?;
                    }
                    StatementKind::Assign(box (target, _)) => {
                        let target: utils::Place<'tcx> = (*target).into();
                        // Any references to target should be made old because it
                        // will be overwritten in the assignment.
                        if target.is_ref(self.ctxt)
                            && self.pcg.borrow.graph().contains(target, self.ctxt)
                        {
                            // The permission to the target may have been Read originally.
                            // Now, because it's been made old, the non-old place should be a leaf,
                            // and its permission should be Exclusive.
                            if self.pcg.capabilities.get(target.into())
                                == Some(CapabilityKind::Read)
                            {
                                self.record_and_apply_action(
                                    BorrowPCGAction::restore_capability(
                                        target.into(),
                                        CapabilityKind::Exclusive,
                                    )
                                    .into(),
                                )?;
                            }
                        }

                        if !target.is_owned(self.ctxt) {
                            if let Some(target_cap) = self.pcg.capabilities.get(target.into()) {
                                if target_cap != CapabilityKind::Write {
                                    // TODO
                                    // pcg_validity_assert!(
                                    //     target_cap >= CapabilityKind::Write,
                                    //     "{:?}: {} cap {:?} is not greater than {:?}",
                                    //     location,
                                    //     target.to_short_string(self.ctxt),
                                    //     target_cap,
                                    //     CapabilityKind::Write
                                    // );
                                    self.record_and_apply_action(
                                        BorrowPCGAction::weaken(
                                            target,
                                            target_cap,
                                            Some(CapabilityKind::Write),
                                        )
                                        .into(),
                                    )?;
                                }
                            } else {
                                pcg_validity_assert!(
                                    false,
                                    "No capability found for {:?} in {:?}",
                                    target,
                                    statement,
                                );
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
                                let should_remove = !matches!(
                                    edge.kind(),
                                    BorrowPcgEdgeKind::BorrowPcgExpansion(_)
                                );
                                if should_remove {
                                    self.remove_edge_and_set_latest(edge, location, "Assign")?;
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
            EvalStmtPhase::PostMain => {
                self.stmt_post_main(statement, location)?;
            }
            _ => {}
        }
        Ok(())
    }

    fn stmt_post_main(
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
