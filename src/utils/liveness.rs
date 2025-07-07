use std::{cell::RefCell, rc::Rc};

use derive_more::Deref;

use crate::{
    compute_fixpoint,
    rustc_interface::{
        dataflow::{with_cursor_state, Analysis, AnalysisEngine},
        middle::mir::{
            self,
            visit::{MutatingUseContext, NonMutatingUseContext, PlaceContext, Visitor},
        },
        mir_dataflow::{fmt::DebugWithContext, Backward, GenKill, JoinSemiLattice, ResultsCursor},
    },
    utils::{data_structures::HashSet, CompilerCtxt, Place},
};

#[derive(Clone, Eq, PartialEq, Deref, Debug)]
struct PlaceLivenessDomain<'tcx> {
    places: HashSet<Place<'tcx>>,
}

struct TransferFunction<'a, 'tcx>(pub &'a mut PlaceLivenessDomain<'tcx>);

impl<'tcx> Visitor<'tcx> for TransferFunction<'_, 'tcx> {
    fn visit_place(
        &mut self,
        place: &mir::Place<'tcx>,
        context: PlaceContext,
        location: mir::Location,
    ) {
        if let PlaceContext::MutatingUse(MutatingUseContext::Yield) = context {
            // The resume place is evaluated and assigned to only after coroutine resumes, so its
            // effect is handled separately in `call_resume_effect`.
            return;
        }

        match DefUse::for_place(*place, context) {
            Some(DefUse::Def) => {
                if let PlaceContext::MutatingUse(
                    MutatingUseContext::Call | MutatingUseContext::AsmOutput,
                ) = context
                {
                    // For the associated terminators, this is only a `Def` when the terminator
                    // returns "successfully." As such, we handle this case separately in
                    // `call_return_effect` above. However, if the place looks like `*_5`, this is
                    // still unconditionally a use of `_5`.
                } else {
                    self.0.kill((*place).into());
                }
            }
            Some(DefUse::Use) => self.0.gen_((*place).into()),
            None => {}
        }

        self.visit_projection(place.as_ref(), context, location);
    }

    fn visit_local(&mut self, local: mir::Local, context: PlaceContext, _: mir::Location) {
        DefUse::apply(self.0, local.into(), context);
    }
}

impl<'tcx> GenKill<Place<'tcx>> for PlaceLivenessDomain<'tcx> {
    fn gen_(&mut self, elem: Place<'tcx>) {
        self.places.retain(|p| !p.conflicts_with(elem));
        self.places.insert(elem);
    }

    fn kill(&mut self, elem: Place<'tcx>) {
        self.places.retain(|p| !p.conflicts_with(elem));
    }
}

impl<'tcx> JoinSemiLattice for PlaceLivenessDomain<'tcx> {
    fn join(&mut self, other: &Self) -> bool {
        let mut changed = false;
        for place in other.places.iter() {
            if !self.places.contains(place) {
                self.places.insert(place.clone());
                changed = true;
            }
        }
        changed
    }
}

struct PlaceLivenessAnalysis;

impl<'tcx> Analysis<'tcx> for PlaceLivenessAnalysis {
    type Domain = PlaceLivenessDomain<'tcx>;
    type Direction = Backward;

    const NAME: &'static str = "place_liveness";

    fn bottom_value(&self, body: &mir::Body<'tcx>) -> Self::Domain {
        PlaceLivenessDomain {
            places: Default::default(),
        }
    }

    fn initialize_start_block(&self, _body: &mir::Body<'tcx>, state: &mut Self::Domain) {}

    fn apply_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &mir::Statement<'tcx>,
        location: mir::Location,
    ) {
        TransferFunction(state).visit_statement(statement, location);
    }

    fn apply_terminator_effect<'mir>(
        &mut self,
        state: &mut Self::Domain,
        terminator: &'mir mir::Terminator<'tcx>,
        location: mir::Location,
    ) -> mir::TerminatorEdges<'mir, 'tcx> {
        TransferFunction(state).visit_terminator(terminator, location);
        terminator.edges()
    }
}

pub(crate) struct PlaceLiveness<'mir, 'tcx> {
    cursor: Rc<RefCell<ResultsCursor<'mir, 'tcx, AnalysisEngine<PlaceLivenessAnalysis>>>>,
}

impl<'tcx> DebugWithContext<AnalysisEngine<PlaceLivenessAnalysis>> for PlaceLivenessDomain<'tcx> {}

impl<'mir, 'tcx> PlaceLiveness<'mir, 'tcx> {
    pub(crate) fn new(ctxt: CompilerCtxt<'mir, 'tcx>) -> Self {
        Self {
            cursor: Rc::new(RefCell::new(
                compute_fixpoint(
                    AnalysisEngine(PlaceLivenessAnalysis),
                    ctxt.tcx(),
                    ctxt.body(),
                )
                .into_results_cursor(ctxt.body()),
            )),
        }
    }
    pub(crate) fn is_live(&self, place: Place<'tcx>, location: mir::Location) -> bool {
        let mut cursor = self.cursor.as_ref().borrow_mut();
        cursor.seek_before_primary_effect(location);
        with_cursor_state(cursor, |state| state.contains(&place))
    }
}

#[derive(Eq, PartialEq, Clone)]
enum DefUse {
    Def,
    Use,
}

impl DefUse {
    fn apply<'tcx>(
        state: &mut PlaceLivenessDomain<'tcx>,
        place: mir::Place<'tcx>,
        context: PlaceContext,
    ) {
        match DefUse::for_place(place, context) {
            Some(DefUse::Def) => state.kill(place.into()),
            Some(DefUse::Use) => state.gen_(place.into()),
            None => {}
        }
    }

    fn for_place(place: mir::Place<'_>, context: PlaceContext) -> Option<DefUse> {
        match context {
            PlaceContext::NonUse(_) => None,

            PlaceContext::MutatingUse(
                MutatingUseContext::Call
                | MutatingUseContext::Yield
                | MutatingUseContext::AsmOutput
                | MutatingUseContext::Store
                | MutatingUseContext::Deinit,
            ) => {
                if place.is_indirect() {
                    // Treat derefs as a use of the base local. `*p = 4` is not a def of `p` but a
                    // use.
                    Some(DefUse::Use)
                } else if place.projection.is_empty() {
                    Some(DefUse::Def)
                } else {
                    None
                }
            }

            // Setting the discriminant is not a use because it does no reading, but it is also not
            // a def because it does not overwrite the whole place
            PlaceContext::MutatingUse(MutatingUseContext::SetDiscriminant) => {
                place.is_indirect().then_some(DefUse::Use)
            }

            // All other contexts are uses...
            PlaceContext::MutatingUse(
                MutatingUseContext::RawBorrow
                | MutatingUseContext::Borrow
                | MutatingUseContext::Drop
                | MutatingUseContext::Retag,
            )
            | PlaceContext::NonMutatingUse(
                NonMutatingUseContext::RawBorrow
                | NonMutatingUseContext::Copy
                | NonMutatingUseContext::Inspect
                | NonMutatingUseContext::Move
                | NonMutatingUseContext::PlaceMention
                | NonMutatingUseContext::FakeBorrow
                | NonMutatingUseContext::SharedBorrow,
            ) => Some(DefUse::Use),

            PlaceContext::MutatingUse(MutatingUseContext::Projection)
            | PlaceContext::NonMutatingUse(NonMutatingUseContext::Projection) => {
                unreachable!("A projection could be a def or a use and must be handled separately")
            }
        }
    }
}
