// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::rc::Rc;

use rustc_interface::{
    dataflow::Analysis,
    middle::mir::{visit::Visitor, Body, Location, Statement, Terminator, TerminatorEdges},
};

use crate::{rustc_interface, utils::PlaceRepacker};

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
        let mut tw = TripleWalker::default();
        tw.visit_terminator(terminator, location);
        self.apply_main(state, tw, location);
        terminator.edges()
    }
}

impl<'a, 'tcx> FpcsEngine<'a, 'tcx> {
    fn apply_before(
        &self,
        state: &mut FreePlaceCapabilitySummary<'a, 'tcx>,
        tw: TripleWalker<'tcx>,
        location: Location,
    ) {
        if let Some(error) = tw.error {
            state.error = Some(error);
            return;
        }
        state.data.enter_location(location);
        // Repack for operands
        state.data.states.pre_operands = state.data.states.post_main.clone();
        for &triple in &tw.operand_triples {
            let triple = triple.replace_place(self.repacker);
            let pre_operands = Rc::<_>::make_mut(&mut state.data.states.pre_operands);
            if let Err(e) = pre_operands.requires(triple.pre(), self.repacker) {
                state.error = Some(e);
                return;
            }
        }

        // Apply operands effects
        state.data.states.post_operands = state.data.states.pre_operands.clone();
        for triple in tw.operand_triples {
            let post_operands = Rc::<_>::make_mut(&mut state.data.states.post_operands);
            let triple = triple.replace_place(self.repacker);
            post_operands.ensures(triple, self.repacker);
        }
    }

    fn apply_main(
        &self,
        state: &mut FreePlaceCapabilitySummary<'a, 'tcx>,
        tw: TripleWalker<'tcx>,
        _location: Location,
    ) {
        if let Some(error) = tw.error {
            state.error = Some(error);
            return;
        }
        // Repack for main
        state.data.states.pre_main = state.data.states.post_operands.clone();
        for &triple in &tw.main_triples {
            let triple = triple.replace_place(self.repacker);
            let pre_main = Rc::<_>::make_mut(&mut state.data.states.pre_main);
            if let Err(e) = pre_main.requires(triple.pre(), self.repacker) {
                state.error = Some(e);
                return;
            }
        }

        // Apply main effects
        state.data.states.post_main = state.data.states.pre_main.clone();
        for triple in tw.main_triples {
            let triple = triple.replace_place(self.repacker);
            let post_main = Rc::<_>::make_mut(&mut state.data.states.post_main);
            post_main.ensures(triple, self.repacker);
        }
    }
}
