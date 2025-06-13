#[rustversion::since(2024-11-14)]
use super::mir_dataflow::Analysis as MirAnalysis;

use super::{
    middle::{
        mir::{
            self, BasicBlock, Body, CallReturnPlaces, Location, Statement, Terminator,
            TerminatorEdges,
        },
        ty,
    },
    mir_dataflow,
};

#[rustversion::since(2025-05-24)]
pub struct AnalysisAndResults<'tcx, A>
where
    A: mir_dataflow::Analysis<'tcx>,
{
    analysis: A,
    results: mir_dataflow::Results<A::Domain>,
}

impl<'tcx, A> AnalysisAndResults<'tcx, A>
where
    A: mir_dataflow::Analysis<'tcx>,
{
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

    #[rustversion::before(2025-05-24)]
    pub fn entry_set_for_block(&self, block: BasicBlock) -> &A::Domain {
        self.results.entry_set_for_block(block)
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
    results: mir_dataflow::Results<'tcx, A>,
}
pub trait Analysis<'tcx> {
    const NAME: &'static str;
    type Domain: mir_dataflow::JoinSemiLattice + Clone;

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

#[rustversion::before(2024-11-14)]
pub(crate) fn compute_fixpoint<'tcx, T: mir_dataflow::Analysis<'tcx>>(
    analysis: T,
    tcx: ty::TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> AnalysisAndResults<'tcx, T>
where
    T: Sized,
    <T as mir_dataflow::AnalysisDomain<'tcx>>::Domain: mir_dataflow::fmt::DebugWithContext<T>,
{
    let engine = mir_dataflow::Engine::new_generic(tcx, body, analysis);
    let results = engine.pass_name("pcg").iterate_to_fixpoint();
    AnalysisAndResults { results }
}

#[rustversion::all(before(2025-05-24), since(2024-11-14))]
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

#[rustversion::all(since(2025-05-24))]
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

#[derive(Debug, Eq, PartialEq)]
pub struct AnalysisEngine<T>(pub(crate) T);

#[rustversion::before(2024-11-14)]
impl<'tcx, T: Analysis<'tcx>> mir_dataflow::AnalysisDomain<'tcx> for AnalysisEngine<T> {
    type Domain = T::Domain;
    const NAME: &'static str = T::NAME;

    fn bottom_value(&self, body: &Body<'tcx>) -> Self::Domain {
        self.0.bottom_value(body)
    }

    fn initialize_start_block(&self, body: &Body<'tcx>, state: &mut Self::Domain) {
        self.0.initialize_start_block(body, state);
    }
}
impl<'tcx, T: Analysis<'tcx>> mir_dataflow::Analysis<'tcx> for AnalysisEngine<T> {
    #[rustversion::since(2024-11-14)]
    const NAME: &'static str = T::NAME;

    #[rustversion::since(2024-11-14)]
    type Domain = T::Domain;

    #[rustversion::since(2024-11-14)]
    fn bottom_value(&self, body: &mir::Body<'tcx>) -> Self::Domain {
        self.0.bottom_value(body)
    }

    #[rustversion::since(2024-11-14)]
    fn initialize_start_block(&self, body: &Body<'tcx>, state: &mut Self::Domain) {
        self.0.initialize_start_block(body, state);
    }

    #[rustversion::before(2024-12-14)]
    fn apply_before_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &mir::Statement<'tcx>,
        location: Location,
    ) {
        self.0
            .apply_before_statement_effect(state, statement, location);
    }

    #[rustversion::since(2024-12-14)]
    fn apply_early_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &mir::Statement<'tcx>,
        location: Location,
    ) {
        self.0
            .apply_before_statement_effect(state, statement, location);
    }

    #[rustversion::before(2024-12-14)]
    fn apply_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &mir::Statement<'tcx>,
        location: Location,
    ) {
        self.0.apply_statement_effect(state, statement, location);
    }

    #[rustversion::since(2024-12-14)]
    fn apply_primary_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &mir::Statement<'tcx>,
        location: Location,
    ) {
        self.0.apply_statement_effect(state, statement, location);
    }

    #[rustversion::before(2024-12-14)]
    fn apply_terminator_effect<'mir>(
        &mut self,
        state: &mut Self::Domain,
        terminator: &'mir mir::Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        self.0.apply_terminator_effect(state, terminator, location)
    }

    #[rustversion::since(2024-12-14)]
    fn apply_primary_terminator_effect<'mir>(
        &mut self,
        state: &mut Self::Domain,
        terminator: &'mir mir::Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        self.0.apply_terminator_effect(state, terminator, location)
    }

    #[rustversion::before(2024-12-14)]
    fn apply_before_terminator_effect(
        &mut self,
        state: &mut Self::Domain,
        terminator: &mir::Terminator<'tcx>,
        location: Location,
    ) {
        self.0
            .apply_before_terminator_effect(state, terminator, location)
    }

    #[rustversion::since(2024-12-14)]
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
