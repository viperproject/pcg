use std::cell::RefMut;

use derive_more::Deref;

use super::mir_dataflow::{self, ResultsCursor};

use super::mir_dataflow::Analysis as MirAnalysis;

use super::middle::{
    mir::{
        self, BasicBlock, Body, CallReturnPlaces, Location, Statement, Terminator, TerminatorEdges,
    },
    ty,
};

#[rustversion::since(2025-05-24)]
pub struct AnalysisAndResults<'tcx, A>
where
    A: mir_dataflow::Analysis<'tcx>,
{
    analysis: A,
    pub(crate) results: mir_dataflow::Results<A::Domain>,
}

impl<'tcx, A> AnalysisAndResults<'tcx, A>
where
    A: mir_dataflow::Analysis<'tcx>,
{
    #[rustversion::since(2025-05-24)]
    pub fn get_analysis(&self) -> &A {
        &self.analysis
    }

    #[rustversion::before(2025-05-24)]
    pub fn get_analysis(&self) -> &A {
        &self.results.analysis
    }

    #[rustversion::since(2025-05-24)]
    pub fn into_results_cursor<'mir>(
        self,
        body: &'mir Body<'tcx>,
    ) -> mir_dataflow::ResultsCursor<'mir, 'tcx, A> {
        mir_dataflow::ResultsCursor::new_owning(body, self.analysis, self.results)
    }

    #[rustversion::since(2025-05-24)]
    pub fn entry_set_for_block(&self, block: BasicBlock) -> &A::Domain {
        &self.results[block]
    }

    #[rustversion::since(2025-05-24)]
    pub fn entry_state_for_block_mut(&mut self, block: BasicBlock) -> &mut A::Domain {
        &mut self.results[block]
    }

    #[rustversion::before(2025-05-24)]
    pub fn entry_set_for_block(&self, block: BasicBlock) -> &A::Domain {
        self.results.entry_set_for_block(block)
    }

    #[rustversion::before(2025-05-24)]
    pub fn entry_state_for_block_mut(&mut self, block: BasicBlock) -> &mut A::Domain {
        &mut self.results.entry_states[block]
    }

    #[rustversion::before(2025-05-24)]
    pub fn into_results_cursor<'mir>(
        self,
        body: &'mir Body<'tcx>,
    ) -> mir_dataflow::ResultsCursor<'mir, 'tcx, A> {
        self.results.into_results_cursor(body)
    }
}

#[rustversion::before(2025-05-24)]
pub struct AnalysisAndResults<'tcx, A>
where
    A: mir_dataflow::Analysis<'tcx>,
{
    pub(crate) results: mir_dataflow::Results<'tcx, A>,
}
pub trait Analysis<'tcx> {
    const NAME: &'static str;
    type Domain: mir_dataflow::JoinSemiLattice + Clone;
    type Direction: mir_dataflow::Direction;

    fn bottom_value(&self, body: &mir::Body<'tcx>) -> Self::Domain;

    fn initialize_start_block(&self, _body: &Body<'tcx>, state: &mut Self::Domain);

    #[tracing::instrument(skip(self, _state, _statement))]
    fn apply_before_statement_effect(
        &mut self,
        _state: &mut Self::Domain,
        _statement: &Statement<'tcx>,
        location: Location,
    ) {
    }

    fn apply_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    );

    fn apply_before_terminator_effect(
        &mut self,
        _state: &mut Self::Domain,
        _terminator: &Terminator<'tcx>,
        _location: Location,
    ) {
    }

    fn apply_terminator_effect<'mir>(
        &mut self,
        state: &mut Self::Domain,
        terminator: &'mir Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx>;
}

#[rustversion::before(2025-05-24)]
pub(crate) fn compute_fixpoint<'tcx, T: Sized + mir_dataflow::Analysis<'tcx>>(
    analysis: T,
    tcx: ty::TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> AnalysisAndResults<'tcx, T>
where
    <T as mir_dataflow::Analysis<'tcx>>::Domain: mir_dataflow::fmt::DebugWithContext<T>,
{
    AnalysisAndResults {
        results: MirAnalysis::iterate_to_fixpoint(analysis, tcx, body, None),
    }
}

#[rustversion::since(2025-05-24)]
pub(crate) fn compute_fixpoint<'tcx, T: Sized + mir_dataflow::Analysis<'tcx>>(
    analysis: T,
    tcx: ty::TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> AnalysisAndResults<'tcx, T>
where
    <T as mir_dataflow::Analysis<'tcx>>::Domain: mir_dataflow::fmt::DebugWithContext<T>,
{
    let results = MirAnalysis::iterate_to_fixpoint(analysis, tcx, body, None);
    AnalysisAndResults {
        analysis: results.analysis,
        results: results.results,
    }
}

#[derive(Deref, Debug, Eq, PartialEq)]
pub struct AnalysisEngine<T>(pub(crate) T);

impl<'tcx, T: Analysis<'tcx>> mir_dataflow::Analysis<'tcx> for AnalysisEngine<T> {
    type Direction = T::Direction;

    const NAME: &'static str = T::NAME;

    type Domain = T::Domain;

    fn bottom_value(&self, body: &mir::Body<'tcx>) -> Self::Domain {
        self.0.bottom_value(body)
    }

    fn initialize_start_block(&self, body: &Body<'tcx>, state: &mut Self::Domain) {
        self.0.initialize_start_block(body, state);
    }

    fn apply_early_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &mir::Statement<'tcx>,
        location: Location,
    ) {
        self.0
            .apply_before_statement_effect(state, statement, location);
    }

    fn apply_primary_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &mir::Statement<'tcx>,
        location: Location,
    ) {
        self.0.apply_statement_effect(state, statement, location);
    }

    fn apply_primary_terminator_effect<'mir>(
        &mut self,
        state: &mut Self::Domain,
        terminator: &'mir mir::Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        self.0.apply_terminator_effect(state, terminator, location)
    }

    fn apply_early_terminator_effect(
        &mut self,
        state: &mut Self::Domain,
        terminator: &mir::Terminator<'tcx>,
        location: Location,
    ) {
        self.0
            .apply_before_terminator_effect(state, terminator, location)
    }

    fn apply_call_return_effect(
        &mut self,
        _state: &mut Self::Domain,
        _block: BasicBlock,
        _return_places: CallReturnPlaces<'_, 'tcx>,
    ) {
    }
}

pub(crate) fn with_cursor_state<'tcx, A: mir_dataflow::Analysis<'tcx>, R>(
    cursor: RefMut<'_, ResultsCursor<'_, 'tcx, A>>,
    f: impl FnOnce(&A::Domain) -> R,
) -> R {
    f(cursor.get())
}
