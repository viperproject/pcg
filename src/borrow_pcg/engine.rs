use std::rc::Rc;

use crate::{
    combined_pcs::{EvalStmtPhase, PCGError},
    rustc_interface::{
        borrowck::PoloniusOutput,
        middle::{
            mir::{visit::Visitor, Body, Location, Statement, Terminator, TerminatorEdges},
            ty::TyCtxt,
        },
    },
    utils::display::DisplayDiff,
};

use super::{
    state::BorrowsState,
    visitor::{BorrowsVisitor, StatementStage},
};
use crate::borrow_pcg::domain::BorrowsDomain;
use crate::utils::eval_stmt_data::EvalStmtData;
use crate::utils::PlaceRepacker;

pub struct BorrowsEngine<'mir, 'tcx> {
    pub(crate) tcx: TyCtxt<'tcx>,
    pub(crate) body: &'mir Body<'tcx>,
    pub(crate) output_facts: Option<&'mir PoloniusOutput>,
}

impl<'mir, 'tcx> BorrowsEngine<'mir, 'tcx> {
    pub(crate) fn new(
        tcx: TyCtxt<'tcx>,
        body: &'mir Body<'tcx>,
        output_facts: Option<&'mir PoloniusOutput>,
    ) -> Self {
        BorrowsEngine {
            tcx,
            body,
            output_facts,
        }
    }
}

impl<'a, 'tcx> BorrowsEngine<'a, 'tcx> {
    pub(crate) fn prepare_operands(
        &mut self,
        state: &mut BorrowsDomain<'a, 'tcx>,
        statement: &Statement<'tcx>,
        location: Location,
    ) -> Result<(), PCGError> {
        state.data.enter_location(location);

        state.data.states.0.pre_operands = state.data.states.0.post_main.clone();
        BorrowsVisitor::preparing(self, state, StatementStage::Operands)
            .visit_statement(statement, location);
        if let Some(error) = state.error() {
            return Err(error.clone());
        }

        if !state.actions.pre_operands.is_empty() {
            state.data.states.0.pre_operands = state.data.states.0.post_main.clone();
        } else if !state.has_error()
            && state.data.states.0.pre_operands != state.data.states.0.post_main
        {
            panic!(
                "{:?}: No actions were emitted, but the state has changed:\n{}",
                location,
                state.data.entry_state.fmt_diff(
                    state.data.states[EvalStmtPhase::PreOperands].as_ref(),
                    PlaceRepacker::new(self.body, self.tcx)
                )
            );
        }
        Ok(())
    }

    pub(crate) fn apply_operands(
        &mut self,
        state: &mut BorrowsDomain<'a, 'tcx>,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        BorrowsVisitor::applying(self, state, StatementStage::Operands)
            .visit_statement(statement, location);
        state.data.states.0.post_operands = state.data.states.0.post_main.clone();
    }

    pub(crate) fn apply_statement_effect(
        &mut self,
        state: &mut BorrowsDomain<'a, 'tcx>,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        if state.has_error() {
            return;
        }
        BorrowsVisitor::preparing(self, state, StatementStage::Main)
            .visit_statement(statement, location);
        state.data.states.0.pre_main = state.data.states.0.post_main.clone();
        BorrowsVisitor::applying(self, state, StatementStage::Main)
            .visit_statement(statement, location);
    }

    pub(crate) fn apply_before_terminator_effect(
        &mut self,
        state: &mut BorrowsDomain<'a, 'tcx>,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) {
        if state.has_error() {
            return;
        }
        state.data.enter_location(location);
        BorrowsVisitor::preparing(self, state, StatementStage::Operands)
            .visit_terminator(terminator, location);
        state.data.pre_operands_complete();
        BorrowsVisitor::applying(self, state, StatementStage::Operands)
            .visit_terminator(terminator, location);
        state.data.post_operands_complete();
    }

    pub(crate) fn apply_terminator_effect<'mir>(
        &mut self,
        state: &mut BorrowsDomain<'a, 'tcx>,
        terminator: &'mir Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        if state.has_error() {
            return terminator.edges();
        }
        BorrowsVisitor::preparing(self, state, StatementStage::Main)
            .visit_terminator(terminator, location);
        state.data.pre_main_complete();
        BorrowsVisitor::applying(self, state, StatementStage::Main)
            .visit_terminator(terminator, location);
        terminator.edges()
    }
}

pub(crate) type BorrowsStates<'tcx> = EvalStmtData<Rc<BorrowsState<'tcx>>>;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub(crate) enum DataflowPhase {
    Init,
    Join,
    Transfer,
}
