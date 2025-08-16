use crate::error::PcgError;
use crate::rustc_interface::middle::mir::{
    self,
    visit::{self},
};

use super::Place;
#[rustversion::before(2025-03-02)]
use crate::rustc_interface::middle::mir::Mutability;

pub(crate) trait FallableVisitor<'tcx> {
    fn visit_statement_fallable(
        &mut self,
        statement: &mir::Statement<'tcx>,
        location: mir::Location,
    ) -> Result<(), PcgError> {
        self.super_statement_fallable(statement, location)
    }

    fn visit_operand_fallable(
        &mut self,
        operand: &mir::Operand<'tcx>,
        location: mir::Location,
    ) -> Result<(), PcgError> {
        self.super_operand_fallable(operand, location)
    }

    fn super_operand_fallable(
        &mut self,
        operand: &mir::Operand<'tcx>,
        location: mir::Location,
    ) -> Result<(), PcgError> {
        match operand {
            mir::Operand::Copy(place) => {
                self.visit_place_fallable(
                    (*place).into(),
                    visit::PlaceContext::NonMutatingUse(visit::NonMutatingUseContext::Copy),
                    location,
                )?;
            }
            mir::Operand::Move(place) => {
                self.visit_place_fallable(
                    (*place).into(),
                    visit::PlaceContext::NonMutatingUse(visit::NonMutatingUseContext::Move),
                    location,
                )?;
            }
            mir::Operand::Constant(_constant) => {
                // No places to visit in constants
            }
        }
        Ok(())
    }

    #[allow(unreachable_patterns)]
    fn super_statement_fallable(
        &mut self,
        statement: &mir::Statement<'tcx>,
        location: mir::Location,
    ) -> Result<(), PcgError> {
        match &statement.kind {
            mir::StatementKind::Assign(box (place, rvalue)) => {
                self.visit_place_fallable(
                    (*place).into(),
                    visit::PlaceContext::MutatingUse(visit::MutatingUseContext::Store),
                    location,
                )?;
                self.visit_rvalue_fallable(rvalue, location)?;
            }
            mir::StatementKind::FakeRead(box (_, place)) => {
                self.visit_place_fallable(
                    (*place).into(),
                    visit::PlaceContext::NonMutatingUse(visit::NonMutatingUseContext::Inspect),
                    location,
                )?;
            }
            mir::StatementKind::SetDiscriminant { place, .. } => {
                self.visit_place_fallable(
                    (**place).into(),
                    visit::PlaceContext::MutatingUse(visit::MutatingUseContext::SetDiscriminant),
                    location,
                )?;
            }
            mir::StatementKind::Deinit(place) => {
                self.visit_place_fallable(
                    (**place).into(),
                    visit::PlaceContext::MutatingUse(visit::MutatingUseContext::Deinit),
                    location,
                )?;
            }
            mir::StatementKind::StorageLive(_) => {}
            mir::StatementKind::StorageDead(_) => {}
            mir::StatementKind::Retag(_, place) => {
                self.visit_place_fallable(
                    (**place).into(),
                    visit::PlaceContext::MutatingUse(visit::MutatingUseContext::Retag),
                    location,
                )?;
            }
            mir::StatementKind::PlaceMention(place) => {
                self.visit_place_fallable(
                    (**place).into(),
                    visit::PlaceContext::NonMutatingUse(visit::NonMutatingUseContext::PlaceMention),
                    location,
                )?;
            }
            mir::StatementKind::AscribeUserType(box (place, _), variance) => {
                self.visit_place_fallable(
                    (*place).into(),
                    visit::PlaceContext::NonUse(visit::NonUseContext::AscribeUserTy(*variance)),
                    location,
                )?;
            }
            mir::StatementKind::Coverage(_) => {
                // No places to visit
            }
            mir::StatementKind::Intrinsic(box intrinsic) => match intrinsic {
                mir::NonDivergingIntrinsic::Assume(op) => {
                    self.visit_operand_fallable(op, location)?
                }
                mir::NonDivergingIntrinsic::CopyNonOverlapping(copy_info) => {
                    self.visit_operand_fallable(&copy_info.src, location)?;
                    self.visit_operand_fallable(&copy_info.dst, location)?;
                    self.visit_operand_fallable(&copy_info.count, location)?;
                }
            },
            mir::StatementKind::ConstEvalCounter => {
                // No places to visit
            }
            mir::StatementKind::Nop => {
                // No places to visit
            }
            _ => todo!(),
        }
        Ok(())
    }

    fn visit_terminator_fallable(
        &mut self,
        terminator: &mir::Terminator<'tcx>,
        location: mir::Location,
    ) -> Result<(), PcgError> {
        self.super_terminator_fallable(terminator, location)
    }

    fn visit_place_fallable(
        &mut self,
        place: Place<'tcx>,
        context: visit::PlaceContext,
        location: mir::Location,
    ) -> Result<(), PcgError>;

    fn visit_rvalue_fallable(
        &mut self,
        rvalue: &mir::Rvalue<'tcx>,
        location: mir::Location,
    ) -> Result<(), PcgError> {
        self.super_rvalue_fallable(rvalue, location)
    }

    #[allow(unreachable_patterns)]
    fn super_rvalue_fallable(
        &mut self,
        rvalue: &mir::Rvalue<'tcx>,
        location: mir::Location,
    ) -> Result<(), PcgError> {
        match rvalue {
            mir::Rvalue::Use(operand) => {
                self.visit_operand_fallable(operand, location)?;
            }
            mir::Rvalue::Repeat(value, _ct) => {
                self.visit_operand_fallable(value, location)?;
            }
            mir::Rvalue::ThreadLocalRef(_) => {}
            mir::Rvalue::Ref(_, bk, path) => {
                let ctx = match bk {
                    mir::BorrowKind::Shared => visit::PlaceContext::NonMutatingUse(
                        visit::NonMutatingUseContext::SharedBorrow,
                    ),
                    mir::BorrowKind::Fake(_) => visit::PlaceContext::NonMutatingUse(
                        visit::NonMutatingUseContext::FakeBorrow,
                    ),
                    mir::BorrowKind::Mut { .. } => {
                        visit::PlaceContext::MutatingUse(visit::MutatingUseContext::Borrow)
                    }
                };
                self.visit_place_fallable((*path).into(), ctx, location)?;
            }
            mir::Rvalue::CopyForDeref(place) => {
                self.visit_place_fallable(
                    (*place).into(),
                    visit::PlaceContext::NonMutatingUse(visit::NonMutatingUseContext::Inspect),
                    location,
                )?;
            }
            mir::Rvalue::Len(path) => {
                self.visit_place_fallable(
                    (*path).into(),
                    visit::PlaceContext::NonMutatingUse(visit::NonMutatingUseContext::Inspect),
                    location,
                )?;
            }
            mir::Rvalue::Cast(_, operand, _) => {
                self.visit_operand_fallable(operand, location)?;
            }
            mir::Rvalue::BinaryOp(_, box (lhs, rhs)) => {
                self.visit_operand_fallable(lhs, location)?;
                self.visit_operand_fallable(rhs, location)?;
            }
            mir::Rvalue::UnaryOp(_, op) => {
                self.visit_operand_fallable(op, location)?;
            }
            mir::Rvalue::Discriminant(place) => {
                self.visit_place_fallable(
                    (*place).into(),
                    visit::PlaceContext::NonMutatingUse(visit::NonMutatingUseContext::Inspect),
                    location,
                )?;
            }
            mir::Rvalue::NullaryOp(_, _) => {}
            mir::Rvalue::Aggregate(kind, operands) => {
                match &**kind {
                    mir::AggregateKind::Array(_) => {}
                    mir::AggregateKind::Tuple => {}
                    mir::AggregateKind::Adt(_, _, _, _, _) => {}
                    mir::AggregateKind::Closure(_, _) => {}
                    mir::AggregateKind::Coroutine(_, _) => {}
                    mir::AggregateKind::CoroutineClosure(_, _) => {}
                    mir::AggregateKind::RawPtr(_, _) => {}
                }

                for operand in operands {
                    self.visit_operand_fallable(operand, location)?;
                }
            }
            mir::Rvalue::ShallowInitBox(operand, _) => {
                self.visit_operand_fallable(operand, location)?;
            }
            mir::Rvalue::RawPtr(mutability, place) => {
                #[rustversion::since(2025-03-02)]
                let context = match *mutability {
                    mir::RawPtrKind::Mut => {
                        visit::PlaceContext::MutatingUse(visit::MutatingUseContext::RawBorrow)
                    }
                    mir::RawPtrKind::Const => {
                        visit::PlaceContext::NonMutatingUse(visit::NonMutatingUseContext::RawBorrow)
                    }
                    mir::RawPtrKind::FakeForPtrMetadata => {
                        visit::PlaceContext::NonMutatingUse(visit::NonMutatingUseContext::RawBorrow)
                    }
                };
                #[rustversion::before(2025-03-02)]
                let context = match *mutability {
                    Mutability::Mut => {
                        visit::PlaceContext::MutatingUse(visit::MutatingUseContext::RawBorrow)
                    }
                    Mutability::Not => {
                        visit::PlaceContext::NonMutatingUse(visit::NonMutatingUseContext::RawBorrow)
                    }
                };
                self.visit_place_fallable((*place).into(), context, location)?;
            }
            _ => {}
        }
        Ok(())
    }

    fn super_terminator_fallable(
        &mut self,
        terminator: &mir::Terminator<'tcx>,
        location: mir::Location,
    ) -> Result<(), PcgError> {
        match &terminator.kind {
            mir::TerminatorKind::Goto { .. }
            | mir::TerminatorKind::UnwindResume
            | mir::TerminatorKind::UnwindTerminate(_)
            | mir::TerminatorKind::CoroutineDrop
            | mir::TerminatorKind::Unreachable
            | mir::TerminatorKind::FalseEdge { .. }
            | mir::TerminatorKind::FalseUnwind { .. } => Ok(()),
            mir::TerminatorKind::Return => {
                self.visit_place_fallable(
                    mir::RETURN_PLACE.into(),
                    visit::PlaceContext::NonMutatingUse(visit::NonMutatingUseContext::Move),
                    location,
                )?;
                Ok(())
            }
            mir::TerminatorKind::SwitchInt { discr, .. } => {
                self.visit_operand_fallable(discr, location)?;
                Ok(())
            }
            mir::TerminatorKind::Drop { place, .. } => {
                self.visit_place_fallable(
                    (*place).into(),
                    visit::PlaceContext::MutatingUse(visit::MutatingUseContext::Drop),
                    location,
                )?;
                Ok(())
            }
            mir::TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } => {
                self.visit_operand_fallable(func, location)?;
                for arg in args {
                    self.visit_operand_fallable(&arg.node, location)?;
                }
                self.visit_place_fallable(
                    (*destination).into(),
                    visit::PlaceContext::MutatingUse(visit::MutatingUseContext::Call),
                    location,
                )?;
                Ok(())
            }
            mir::TerminatorKind::Assert { cond, .. } => {
                self.visit_operand_fallable(cond, location)?;
                Ok(())
            }
            mir::TerminatorKind::Yield {
                value, resume_arg, ..
            } => {
                self.visit_operand_fallable(value, location)?;
                self.visit_place_fallable(
                    (*resume_arg).into(),
                    visit::PlaceContext::MutatingUse(visit::MutatingUseContext::Yield),
                    location,
                )?;
                Ok(())
            }
            mir::TerminatorKind::InlineAsm { operands, .. } => {
                for op in operands {
                    match op {
                        mir::InlineAsmOperand::In { value, .. } => {
                            self.visit_operand_fallable(value, location)?;
                        }
                        mir::InlineAsmOperand::Out {
                            place: Some(place), ..
                        } => {
                            self.visit_place_fallable(
                                (*place).into(),
                                visit::PlaceContext::MutatingUse(
                                    visit::MutatingUseContext::AsmOutput,
                                ),
                                location,
                            )?;
                        }
                        mir::InlineAsmOperand::InOut {
                            in_value,
                            out_place,
                            ..
                        } => {
                            self.visit_operand_fallable(in_value, location)?;
                            if let Some(out_place) = out_place {
                                self.visit_place_fallable(
                                    (*out_place).into(),
                                    visit::PlaceContext::MutatingUse(
                                        visit::MutatingUseContext::AsmOutput,
                                    ),
                                    location,
                                )?;
                            }
                        }
                        _ => {}
                    }
                }
                Ok(())
            }
            mir::TerminatorKind::TailCall { .. } => todo!(),
        }
    }
}
