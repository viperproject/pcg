// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc_interface::middle::mir::{
    self, Location, Statement, Terminator, TerminatorEdges,
};

use crate::{
    borrow_pcg::state::BorrowsState,
    combined_pcs::{EvalStmtPhase, PcgError},
    rustc_interface,
    utils::{visitor::FallableVisitor, PlaceRepacker},
};

use super::{triple::TripleWalker, FreePlaceCapabilitySummary};

#[derive(Clone)]
pub struct FpcsEngine<'a, 'tcx> {
    pub(crate) repacker: PlaceRepacker<'a, 'tcx>,
}

impl<'a, 'tcx> FpcsEngine<'a, 'tcx> {
    pub(crate) fn apply_before_statement_effect(
        &mut self,
        state: &mut FreePlaceCapabilitySummary<'a, 'tcx>,
        statement: &Statement<'tcx>,
        borrows: &BorrowsState<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        let mut tw = TripleWalker::new(state.repacker);
        tw.visit_statement_fallable(statement, location)?;
        self.apply_before(state, tw, borrows, location)
    }

    pub(crate) fn apply_statement_effect(
        &mut self,
        state: &mut FreePlaceCapabilitySummary<'a, 'tcx>,
        statement: &Statement<'tcx>,
        borrows: &BorrowsState<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        let mut tw = TripleWalker::new(state.repacker);
        tw.visit_statement_fallable(statement, location)?;
        self.apply_main(state, tw, borrows, location)
    }

    pub(crate) fn apply_before_terminator_effect(
        &mut self,
        state: &mut FreePlaceCapabilitySummary<'a, 'tcx>,
        terminator: &Terminator<'tcx>,
        borrows: &BorrowsState<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        let mut tw = TripleWalker::new(state.repacker);
        tw.visit_terminator_fallable(terminator, location)?;
        self.apply_before(state, tw, borrows, location)
    }

    pub(crate) fn apply_terminator_effect<'mir>(
        &mut self,
        state: &mut FreePlaceCapabilitySummary<'a, 'tcx>,
        terminator: &'mir Terminator<'tcx>,
        borrows: &BorrowsState<'tcx>,
        location: Location,
    ) -> Result<TerminatorEdges<'mir, 'tcx>, PcgError> {
        if terminator.kind == mir::TerminatorKind::UnwindResume {
            return Ok(terminator.edges());
        }
        let mut tw = TripleWalker::new(state.repacker);
        tw.visit_terminator_fallable(terminator, location)?;
        state.data.states.0.pre_main = state.data.states.0.post_operands.clone();
        self.apply_main(state, tw, borrows, location)?;
        Ok(terminator.edges())
    }
}

impl<'a, 'tcx> FpcsEngine<'a, 'tcx> {
    #[tracing::instrument(skip(self, state, borrows, tw))]
    fn apply_before(
        &self,
        state: &mut FreePlaceCapabilitySummary<'a, 'tcx>,
        tw: TripleWalker<'a, 'tcx>,
        borrows: &BorrowsState<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        state.actions[EvalStmtPhase::PreOperands].clear();
        // Repack for operands
        state.data.states.0.pre_operands = state.data.states.0.post_main.clone();
        for &triple in &tw.operand_triples {
            let pre_operands = state.data.unwrap_mut(EvalStmtPhase::PreOperands);
            let actions = pre_operands.requires(triple.pre(), self.repacker, borrows)?;
            state.actions[EvalStmtPhase::PreOperands].extend(actions);
        }

        // Apply operands effects
        state.data.states.0.post_operands = state.data.states.0.pre_operands.clone();
        for triple in tw.operand_triples {
            let post_operands = state.data.unwrap_mut(EvalStmtPhase::PostOperands);
            let triple = triple.replace_place(self.repacker);
            post_operands.ensures(triple, self.repacker);
        }
        Ok(())
    }

    #[tracing::instrument(skip(self, state, borrows, tw))]
    fn apply_main(
        &self,
        state: &mut FreePlaceCapabilitySummary<'a, 'tcx>,
        tw: TripleWalker<'a, 'tcx>,
        borrows: &BorrowsState<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        state.actions[EvalStmtPhase::PreMain].clear();
        for &triple in &tw.main_triples {
            let pre_main = state.data.unwrap_mut(EvalStmtPhase::PreMain);
            let actions = pre_main.requires(triple.pre(), self.repacker, borrows)?;
            state.actions[EvalStmtPhase::PreMain].extend(actions);
        }

        // Apply main effects
        state.data.states.0.post_main = state.data.states.0.pre_main.clone();
        for triple in tw.main_triples {
            let post_main = state.data.unwrap_mut(EvalStmtPhase::PostMain);
            post_main.ensures(triple, self.repacker);
        }
        Ok(())
    }
}
