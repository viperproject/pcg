// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc_interface::{
    dataflow::{Analysis, AnalysisDomain},
    middle::mir::{
        visit::Visitor, BasicBlock, Body, CallReturnPlaces, Location, Statement, Terminator,
        TerminatorEdges,
    },
};

use crate::{rustc_interface, utils::PlaceRepacker};

use super::{triple::TripleWalker, FreePlaceCapabilitySummary};

#[derive(Clone, Copy)]
pub struct FpcsEngine<'a, 'tcx>(pub PlaceRepacker<'a, 'tcx>);

impl<'a, 'tcx> AnalysisDomain<'tcx> for FpcsEngine<'a, 'tcx> {
    type Domain = FreePlaceCapabilitySummary<'a, 'tcx>;
    const NAME: &'static str = "free_pcs";

    fn bottom_value(&self, _body: &Body<'tcx>) -> Self::Domain {
        FreePlaceCapabilitySummary::new(self.0)
    }

    fn initialize_start_block(&self, _body: &Body<'tcx>, state: &mut Self::Domain) {
        state.initialize_as_start_block();
    }
}

impl<'a, 'tcx> Analysis<'tcx> for FpcsEngine<'a, 'tcx> {
    fn apply_before_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        let mut tw = TripleWalker::default();
        tw.visit_statement(statement, location);
        self.apply_before(state, tw, location);
    }
    fn apply_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        let mut tw = TripleWalker::default();
        tw.visit_statement(statement, location);
        self.apply_main(state, tw, location);
    }

    fn apply_before_terminator_effect(
        &mut self,
        state: &mut Self::Domain,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) {
        let mut tw = TripleWalker::default();
        tw.visit_terminator(terminator, location);
        self.apply_before(state, tw, location);
    }
    fn apply_terminator_effect<'mir>(
        &mut self,
        state: &mut Self::Domain,
        terminator: &'mir Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        let mut tw = TripleWalker::default();
        tw.visit_terminator(terminator, location);
        self.apply_main(state, tw, location);
        terminator.edges()
    }

    fn apply_call_return_effect(
        &mut self,
        _state: &mut Self::Domain,
        _block: BasicBlock,
        _return_places: CallReturnPlaces<'_, 'tcx>,
    ) {
        // Nothing to do here
    }
}

impl<'a, 'tcx> FpcsEngine<'a, 'tcx> {
    fn apply_before(
        self,
        state: &mut FreePlaceCapabilitySummary<'a, 'tcx>,
        tw: TripleWalker<'tcx>,
        _location: Location,
    ) {
        if let Some(error) = tw.error {
            state.error = Some(error);
            return;
        }
        // Repack for operands
        state.summaries.pre_operands = state.summaries.post_main.clone();
        for &triple in &tw.operand_triples {
            let triple = triple.replace_place(self.0);
            if let Err(e) = state.summaries.pre_operands.requires(triple.pre(), self.0) {
                state.error = Some(e);
                return;
            }
        }

        // Apply operands effects
        state.summaries.post_operands = state.summaries.pre_operands.clone();
        for triple in tw.operand_triples {
            let triple = triple.replace_place(self.0);
            state.summaries.post_operands.ensures(triple, self.0);
        }
    }

    fn apply_main(
        self,
        state: &mut FreePlaceCapabilitySummary<'a, 'tcx>,
        tw: TripleWalker<'tcx>,
        _location: Location,
    ) {
        if let Some(error) = tw.error {
            state.error = Some(error);
            return;
        }
        // Repack for main
        state.summaries.pre_main = state.summaries.post_operands.clone();
        for &triple in &tw.main_triples {
            let triple = triple.replace_place(self.0);
            state
                .summaries
                .pre_main
                .requires(triple.pre(), self.0)
                .unwrap();
        }

        // Apply main effects
        state.summaries.post_main = state.summaries.pre_main.clone();
        for triple in tw.main_triples {
            let triple = triple.replace_place(self.0);
            state.summaries.post_main.ensures(triple, self.0);
        }
    }
}
