use std::rc::Rc;

use crate::{
    pcg::{AnalysisObject, EvalStmtPhase, PcgError},
    rustc_interface::middle::{
        mir::{Body, Location},
        ty::TyCtxt,
    },
    utils::visitor::FallableVisitor,
};

use super::{
    action::actions::BorrowPCGActions,
    coupling_graph_constructor::BorrowCheckerInterface,
    state::BorrowsState,
    visitor::BorrowsVisitor,
};
use crate::utils::eval_stmt_data::EvalStmtData;

pub struct BorrowsEngine<'mir, 'tcx> {
    pub(crate) tcx: TyCtxt<'tcx>,
    pub(crate) body: &'mir Body<'tcx>,
}

impl<'mir, 'tcx> BorrowsEngine<'mir, 'tcx> {
    pub(crate) fn new(tcx: TyCtxt<'tcx>, body: &'mir Body<'tcx>) -> Self {
        BorrowsEngine { tcx, body }
    }
}

impl<'a, 'tcx> BorrowsEngine<'a, 'tcx> {
    pub(crate) fn analyze(
        &mut self,
        state: &mut BorrowsState<'tcx>,
        bc: Rc<dyn BorrowCheckerInterface<'a, 'tcx> + 'a>,
        object: AnalysisObject<'_, 'tcx>,
        phase: EvalStmtPhase,
        location: Location,
    ) -> Result<BorrowPCGActions<'tcx>, PcgError> {
        let mut bv = BorrowsVisitor::new(self, state, bc, phase);
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

pub(crate) type BorrowsStates<'tcx> = EvalStmtData<Rc<BorrowsState<'tcx>>>;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub(crate) enum DataflowPhase {
    Init,
    Join,
    Transfer,
}
