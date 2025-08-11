use std::{cell::RefCell, rc::Rc};

use crate::{
    compute_fixpoint,
    rustc_interface::{
        dataflow::{Analysis, AnalysisEngine, with_cursor_state},
        middle::mir::{
            self,
            visit::{
                MutatingUseContext, NonMutatingUseContext, NonUseContext, PlaceContext, Visitor,
            },
        },
        mir_dataflow::{Backward, GenKill, JoinSemiLattice, ResultsCursor, fmt::DebugWithContext},
    },
    utils::{CompilerCtxt, Place, data_structures::HashSet},
};

#[derive(Clone, Eq, PartialEq, Debug)]
struct PlaceLivenessDomain<'tcx> {
    places: HashSet<Place<'tcx>>,
}

impl<'tcx> PlaceLivenessDomain<'tcx> {
    fn is_live(&self, place: Place<'tcx>) -> bool {
        self.places.iter().any(|p| p.is_prefix_or_postfix_of(place))
    }
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
        self.places.retain(|p| !p.is_prefix_or_postfix_of(elem));
        self.places.insert(elem);
    }

    fn kill(&mut self, elem: Place<'tcx>) {
        self.places.retain(|p| !p.is_prefix_or_postfix_of(elem));
    }
}

impl JoinSemiLattice for PlaceLivenessDomain<'_> {
    fn join(&mut self, other: &Self) -> bool {
        let mut changed = false;
        for place in other.places.iter() {
            if !self.places.contains(place) {
                self.places.insert(*place);
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

    fn bottom_value(&self, _body: &mir::Body<'tcx>) -> Self::Domain {
        PlaceLivenessDomain {
            places: Default::default(),
        }
    }

    fn initialize_start_block(&self, _body: &mir::Body<'tcx>, _state: &mut Self::Domain) {}

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

/// Place liveness analysis based on what currently exists in the compiler.
/// However ours is specialized for information relevant to borrows. In particular,
/// we currently give the drops special treatment.
#[derive(Clone)]
pub(crate) struct PlaceLiveness<'mir, 'tcx> {
    cursor: Rc<RefCell<ResultsCursor<'mir, 'tcx, AnalysisEngine<PlaceLivenessAnalysis>>>>,
}

impl DebugWithContext<AnalysisEngine<PlaceLivenessAnalysis>> for PlaceLivenessDomain<'_> {}

impl<'mir, 'tcx> PlaceLiveness<'mir, 'tcx> {
    pub(crate) fn new<BC: Copy>(ctxt: CompilerCtxt<'mir, 'tcx, BC>) -> Self {
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
        // Because this is a backwards analysis, seeking *after* the primary effect considers
        // the state *before* the statment at the location
        cursor.seek_after_primary_effect(location);
        with_cursor_state(cursor, |state| state.is_live(place))
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
            PlaceContext::NonUse(NonUseContext::StorageDead) => Some(DefUse::Def),
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

            // We don't count drops as use in our analysis because drop
            // implementations can sometimes require that the lifetimes of
            // references within a place to still be active and sometimes not.
            //
            // In the case where the lifetime are allowed to expire, if we treat
            // the drop as a use, the PCG would over-approximate the extent of
            // the lifetime, leading to incorrect graphs. This
            // over-approximation can prevent the construction of the PCG (when
            // the compiler wants to e.g. access a place that the PCG still
            // thinks is borrowed)
            //
            // Instead, by not treating the drop as a use, we under-approximate
            // the extents. However because this only occurs in drops, the PCG construction
            // itself will not fail (we don't currently require lifetimes to be live for drops)
            // However, this is still probably incorrect technically.
            // TODO: We should also identify whether the drop requires lifetimes to be live and count
            // usages accordingly.
            PlaceContext::MutatingUse(MutatingUseContext::Drop) => None,

            // All other contexts are uses...
            PlaceContext::MutatingUse(
                MutatingUseContext::RawBorrow
                | MutatingUseContext::Borrow
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
