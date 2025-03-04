// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::rc::Rc;

use rustc_interface::{
    dataflow::Analysis,
    middle::mir::{self, visit::Visitor, Body, Location, Statement, Terminator, TerminatorEdges},
};

use crate::{combined_pcs::EvalStmtPhase, rustc_interface, utils::PlaceRepacker};

use super::{triple::TripleWalker, CapabilitySummary, FreePlaceCapabilitySummary};

#[derive(Clone)]
pub struct FpcsEngine<'a, 'tcx> {
    pub(crate) repacker: PlaceRepacker<'a, 'tcx>,
    pub(crate) init_capability_summary: Rc<CapabilitySummary<'tcx>>,
}

impl<'a, 'tcx> Analysis<'tcx> for FpcsEngine<'a, 'tcx> {
    type Domain = FreePlaceCapabilitySummary<'a, 'tcx>;
    const NAME: &'static str = "free_pcs";

    fn bottom_value(&self, _body: &Body<'tcx>) -> FreePlaceCapabilitySummary<'a, 'tcx> {
        FreePlaceCapabilitySummary::new(self.repacker, self.init_capability_summary.clone())
    }

    fn initialize_start_block(
        &self,
        _body: &Body<'tcx>,
        state: &mut FreePlaceCapabilitySummary<'a, 'tcx>,
    ) {
        state.initialize_as_start_block();
    }
    fn apply_before_statement_effect(
        &mut self,
        state: &mut FreePlaceCapabilitySummary<'a, 'tcx>,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        let mut tw = TripleWalker::default();
        tw.visit_statement(statement, location);
        self.apply_before(state, tw, location);
    }
    fn apply_statement_effect(
        &mut self,
        state: &mut FreePlaceCapabilitySummary<'a, 'tcx>,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        let mut tw = TripleWalker::default();
        tw.visit_statement(statement, location);
        self.apply_main(state, tw, location);
    }

    fn apply_before_terminator_effect(
        &mut self,
        state: &mut FreePlaceCapabilitySummary<'a, 'tcx>,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) {
        let mut tw = TripleWalker::default();
        tw.visit_terminator(terminator, location);
        self.apply_before(state, tw, location);
    }
    fn apply_terminator_effect<'mir>(
        &mut self,
        state: &mut FreePlaceCapabilitySummary<'a, 'tcx>,
        terminator: &'mir Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        if terminator.kind == mir::TerminatorKind::UnwindResume {
            return terminator.edges();
        }
        let mut tw = TripleWalker::default();
        tw.visit_terminator(terminator, location);
        self.apply_main(state, tw, location);
        terminator.edges()
    }
}

impl<'a, 'tcx> FpcsEngine<'a, 'tcx> {
    #[tracing::instrument(skip(self, state, tw))]
    fn apply_before(
        &self,
        state: &mut FreePlaceCapabilitySummary<'a, 'tcx>,
        tw: TripleWalker<'tcx>,
        location: Location,
    ) {
        state.actions[EvalStmtPhase::PreOperands].clear();
        if let Some(error) = tw.error {
            state.error = Some(error);
            return;
        }
        state.data.enter_location(location);
        // Repack for operands
        state.data.states.0.pre_operands = state.data.states.0.post_main.clone();
        for &triple in &tw.operand_triples {
            let triple = triple.replace_place(self.repacker);
            let pre_operands = state.data.states.get_mut(EvalStmtPhase::PreOperands);
            match pre_operands.requires(triple.pre(), self.repacker) {
                Ok(ops) => {
                    tracing::debug!("Extend PreOperands with {:?}", ops);
                    state.actions[EvalStmtPhase::PreOperands].extend(ops);
                }
                Err(e) => {
                    state.error = Some(e);
                    return;
                }
            }
        }

        // Apply operands effects
        state.data.states.0.post_operands = state.data.states.0.pre_operands.clone();
        for triple in tw.operand_triples {
            let post_operands = state.data.states.get_mut(EvalStmtPhase::PostOperands);
            let triple = triple.replace_place(self.repacker);
            post_operands.ensures(triple, self.repacker);
        }
    }

    #[tracing::instrument(skip(self, state, tw))]
    fn apply_main(
        &self,
        state: &mut FreePlaceCapabilitySummary<'a, 'tcx>,
        tw: TripleWalker<'tcx>,
        location: Location,
    ) {
        state.actions[EvalStmtPhase::PreMain].clear();
        if let Some(error) = tw.error {
            state.error = Some(error);
            return;
        }
        // Repack for main
        state.data.states.0.pre_main = state.data.states.0.post_operands.clone();
        for &triple in &tw.main_triples {
            let triple = triple.replace_place(self.repacker);
            let pre_main = state.data.states.get_mut(EvalStmtPhase::PreMain);
            match pre_main.requires(triple.pre(), self.repacker) {
                Ok(ops) => {
                    tracing::debug!("Extend PreMain with {:?}", ops);
                    state.actions[EvalStmtPhase::PreMain].extend(ops);
                }
                Err(e) => {
                    state.error = Some(e);
                    return;
                }
            }
        }

        // Apply main effects
        state.data.states.0.post_main = state.data.states.0.pre_main.clone();
        for triple in tw.main_triples {
            let triple = triple.replace_place(self.repacker);
            let post_main = state.data.states.get_mut(EvalStmtPhase::PostMain);
            post_main.ensures(triple, self.repacker);
        }
    }
}
