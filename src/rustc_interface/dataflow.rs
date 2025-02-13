use super::{
    middle::mir::{
        self, BasicBlock, Body, CallReturnPlaces, Location, Statement, Terminator, TerminatorEdges,
    },
    mir_dataflow,
};
pub trait Analysis<'tcx> {
    const NAME: &'static str;
    type Domain: mir_dataflow::JoinSemiLattice + Clone;

    fn bottom_value(&self, body: &mir::Body<'tcx>) -> Self::Domain;

    fn initialize_start_block(&self, _body: &Body<'tcx>, state: &mut Self::Domain);

    fn apply_before_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    );

    fn apply_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    );

    fn apply_before_terminator_effect(
        &mut self,
        state: &mut Self::Domain,
        terminator: &Terminator<'tcx>,
        location: Location,
    );

    fn apply_terminator_effect<'mir>(
        &mut self,
        state: &mut Self::Domain,
        terminator: &'mir Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx>;
}

#[derive(Debug, Eq, PartialEq)]
pub struct PCGAnalysis<T>(pub(crate) T);

#[rustversion::before(2024-11-15)]
impl<'tcx, T: Analysis<'tcx>> mir_dataflow::AnalysisDomain<'tcx> for PCGAnalysis<T> {
    type Domain = T::Domain;
    const NAME: &'static str = T::NAME;

    fn bottom_value(&self, body: &Body<'tcx>) -> Self::Domain {
        self.0.bottom_value(body)
    }

    fn initialize_start_block(&self, body: &Body<'tcx>, state: &mut Self::Domain) {
        self.0.initialize_start_block(body, state);
    }
}
impl<'tcx, T: Analysis<'tcx>> mir_dataflow::Analysis<'tcx> for PCGAnalysis<T> {
    #[rustversion::nightly(2024-11-15)]
    type Domain = T::Domain;

    #[rustversion::nightly(2024-11-15)]
    fn bottom_value(&self, body: &mir::Body<'tcx>) -> Self::Domain {
        self.0.bottom_value(body)
    }

    fn apply_before_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &mir::Statement<'tcx>,
        location: Location,
    ) {
        self.0
            .apply_before_statement_effect(state, statement, location);
    }

    fn apply_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &mir::Statement<'tcx>,
        location: Location,
    ) {
        self.0.apply_statement_effect(state, statement, location);
    }

    fn apply_terminator_effect<'mir>(
        &mut self,
        state: &mut Self::Domain,
        terminator: &'mir mir::Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        self.0.apply_terminator_effect(state, terminator, location)
    }

    fn apply_before_terminator_effect(
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
