use crate::{
    action::PcgActions, pcg::{AnalysisObject, EvalStmtPhase, Pcg, PcgError}, rustc_interface::middle::mir::Location, utils::{visitor::FallableVisitor, CompilerCtxt}
};

use super::{action::actions::BorrowPCGActions, visitor::BorrowsVisitor};

pub struct BorrowsEngine<'mir, 'tcx> {
    pub(crate) ctxt: CompilerCtxt<'mir, 'tcx>,
}

impl<'mir, 'tcx> BorrowsEngine<'mir, 'tcx> {
    pub(crate) fn new(ctxt: CompilerCtxt<'mir, 'tcx>) -> Self {
        BorrowsEngine { ctxt }
    }
}

impl<'tcx> BorrowsEngine<'_, 'tcx> {
    pub(crate) fn analyze(
        &mut self,
        state: &mut Pcg<'tcx>,
        object: AnalysisObject<'_, 'tcx>,
        phase: EvalStmtPhase,
        location: Location,
    ) -> Result<PcgActions<'tcx>, PcgError> {
        let mut bv = BorrowsVisitor::new(
            self,
            &mut state.borrow,
            &mut state.capabilities,
            &state.owned,
            phase,
        );
        match object {
            AnalysisObject::Statement(statement) => {
                bv.visit_statement_fallable(statement, location)?;
            }
            AnalysisObject::Terminator(terminator) => {
                bv.visit_terminator_fallable(terminator, location)?;
            }
        }
        Ok(bv.actions)
    }
}
