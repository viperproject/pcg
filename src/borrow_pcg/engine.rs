use std::rc::Rc;

use crate::{
    pcg::{AnalysisObject, EvalStmtPhase, Pcg, PcgError},
    rustc_interface::middle::mir::Location,
    utils::{visitor::FallableVisitor, CompilerCtxt},
};

use super::{
    action::actions::BorrowPCGActions, coupling_graph_constructor::BorrowCheckerInterface,
    visitor::BorrowsVisitor,
};

pub struct BorrowsEngine<'mir, 'tcx> {
    pub(crate) ctxt: CompilerCtxt<'mir, 'tcx>,
}

impl<'mir, 'tcx> BorrowsEngine<'mir, 'tcx> {
    pub(crate) fn new(ctxt: CompilerCtxt<'mir, 'tcx>) -> Self {
        BorrowsEngine { ctxt }
    }
}

impl<'a, 'tcx> BorrowsEngine<'a, 'tcx> {
    pub(crate) fn analyze(
        &mut self,
        state: &mut Pcg<'tcx>,
        bc: Rc<dyn BorrowCheckerInterface<'a, 'tcx> + 'a>,
        object: AnalysisObject<'_, 'tcx>,
        phase: EvalStmtPhase,
        location: Location,
    ) -> Result<BorrowPCGActions<'tcx>, PcgError> {
        let mut bv =
            BorrowsVisitor::new(self, &mut state.borrow, &mut state.capabilities, bc, phase);
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
