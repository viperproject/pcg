use std::rc::Rc;

use rustc_interface::{
    borrowck::{
        borrow_set::BorrowSet,
        consumers::{LocationTable, PoloniusInput, PoloniusOutput, RegionInferenceContext},
    },
    dataflow::{Analysis, AnalysisDomain, JoinSemiLattice},
    middle::{
        mir::{
            visit::Visitor, BasicBlock, Body, CallReturnPlaces, Location, Statement, Terminator,
            TerminatorEdges,
        },
        ty::{self, TyCtxt},
    },
};
use serde_json::{json, Value};

use crate::{
    borrows::domain::ToJsonWithRepacker,
    rustc_interface,
    utils::{self, Place, PlaceRepacker},
};

use super::{
    borrows_state::BorrowsState, borrows_visitor::BorrowsVisitor, domain::MaybeRemotePlace,
    path_condition::PathCondition,
};
use super::{
    deref_expansion::DerefExpansion,
    domain::{MaybeOldPlace, Reborrow},
};

pub struct BorrowsEngine<'mir, 'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub body: &'mir Body<'tcx>,
    pub location_table: &'mir LocationTable,
    pub input_facts: &'mir PoloniusInput,
    pub borrow_set: Rc<BorrowSet<'tcx>>,
    pub region_inference_context: Rc<RegionInferenceContext<'tcx>>,
    pub output_facts: &'mir PoloniusOutput,
}

impl<'mir, 'tcx> BorrowsEngine<'mir, 'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        body: &'mir Body<'tcx>,
        location_table: &'mir LocationTable,
        input_facts: &'mir PoloniusInput,
        borrow_set: Rc<BorrowSet<'tcx>>,
        region_inference_context: Rc<RegionInferenceContext<'tcx>>,
        output_facts: &'mir PoloniusOutput,
    ) -> Self {
        BorrowsEngine {
            tcx,
            body,
            location_table,
            input_facts,
            borrow_set,
            region_inference_context,
            output_facts,
        }
    }
}

#[derive(Clone, Debug)]
pub enum ReborrowAction<'tcx> {
    AddReborrow(Reborrow<'tcx>),
    RemoveReborrow(Reborrow<'tcx>),
    ExpandPlace(DerefExpansion<'tcx>),
    CollapsePlace(Vec<utils::Place<'tcx>>, MaybeOldPlace<'tcx>),
}

impl<'tcx> ReborrowAction<'tcx> {
    pub fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        match self {
            ReborrowAction::AddReborrow(reborrow) => json!({
                "action": "AddReborrow",
                "reborrow": reborrow.to_json(repacker)
            }),
            ReborrowAction::RemoveReborrow(reborrow) => json!({
                "action": "RemoveReborrow",
                "reborrow": reborrow.to_json(repacker)
            }),
            ReborrowAction::ExpandPlace(e) => json!({
                "action": "ExpandPlace",
                "place": e.base().to_json(repacker),
            }),
            ReborrowAction::CollapsePlace(_, place) => json!({
                "action": "CollapsePlace",
                "place": place.to_json(repacker),
            }),
        }
    }
}

impl<'mir, 'tcx> JoinSemiLattice for BorrowsDomain<'mir, 'tcx> {
    fn join(&mut self, other: &Self) -> bool {
        let mut other_after = other.after.clone();

        // For edges in the other graph that actually belong to it,
        // add the path condition that leads them to this block
        let pc = PathCondition::new(other.block(), self.block());
        other_after.add_path_condition(pc);

        // Overlay both graphs
        self.after.join(
            &other_after,
            self.block(),
            other.block(),
            self.output_facts.as_ref(),
            self.location_table.as_ref(),
            self.repacker,
        )
    }
}

impl<'tcx, 'a> AnalysisDomain<'tcx> for BorrowsEngine<'a, 'tcx> {
    type Domain = BorrowsDomain<'a, 'tcx>;
    const NAME: &'static str = "borrows";

    fn bottom_value(&self, _body: &Body<'tcx>) -> Self::Domain {
        todo!()
    }

    fn initialize_start_block(&self, _body: &Body<'tcx>, _state: &mut Self::Domain) {
        todo!()
    }
}

impl<'a, 'tcx> Analysis<'tcx> for BorrowsEngine<'a, 'tcx> {
    fn apply_before_statement_effect(
        &mut self,
        state: &mut BorrowsDomain<'a, 'tcx>,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        BorrowsVisitor::preparing(self, state, true).visit_statement(statement, location);
        state.before_start = state.after.clone();
        BorrowsVisitor::applying(self, state, true).visit_statement(statement, location);
        state.before_after = state.after.clone();
    }

    fn apply_statement_effect(
        &mut self,
        state: &mut BorrowsDomain<'a, 'tcx>,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        BorrowsVisitor::preparing(self, state, false).visit_statement(statement, location);
        state.start = state.after.clone();
        BorrowsVisitor::applying(self, state, false).visit_statement(statement, location);
    }

    fn apply_before_terminator_effect(
        &mut self,
        state: &mut BorrowsDomain<'a, 'tcx>,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) {
        BorrowsVisitor::preparing(self, state, true).visit_terminator(terminator, location);
        state.before_start = state.after.clone();
        BorrowsVisitor::applying(self, state, true).visit_terminator(terminator, location);
        state.before_after = state.after.clone();
    }

    fn apply_terminator_effect<'mir>(
        &mut self,
        state: &mut BorrowsDomain<'a, 'tcx>,
        terminator: &'mir Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        BorrowsVisitor::preparing(self, state, false).visit_terminator(terminator, location);
        state.start = state.after.clone();
        BorrowsVisitor::applying(self, state, false).visit_terminator(terminator, location);
        terminator.edges()
    }

    fn apply_call_return_effect(
        &mut self,
        _state: &mut Self::Domain,
        _block: BasicBlock,
        _return_places: CallReturnPlaces<'_, 'tcx>,
    ) {
        todo!()
    }
}
#[derive(Clone)]
pub struct BorrowsDomain<'mir, 'tcx> {
    pub before_start: BorrowsState<'tcx>,
    pub before_after: BorrowsState<'tcx>,
    pub start: BorrowsState<'tcx>,
    pub after: BorrowsState<'tcx>,
    pub block: Option<BasicBlock>,
    pub repacker: PlaceRepacker<'mir, 'tcx>,
    pub output_facts: Rc<PoloniusOutput>,
    pub location_table: Rc<LocationTable>,
}

impl<'mir, 'tcx> PartialEq for BorrowsDomain<'mir, 'tcx> {
    fn eq(&self, other: &Self) -> bool {
        self.before_start == other.before_start
            && self.before_after == other.before_after
            && self.start == other.start
            && self.after == other.after
            && self.block == other.block
    }
}

impl<'mir, 'tcx> Eq for BorrowsDomain<'mir, 'tcx> {}

impl<'mir, 'tcx> std::fmt::Debug for BorrowsDomain<'mir, 'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BorrowsDomain")
            .field("before_start", &self.before_start)
            .field("before_after", &self.before_after)
            .field("start", &self.start)
            .field("after", &self.after)
            .field("block", &self.block)
            .finish()
    }
}

impl<'mir, 'tcx> BorrowsDomain<'mir, 'tcx> {
    pub fn is_initialized(&self) -> bool {
        self.block.is_some()
    }

    pub fn set_block(&mut self, block: BasicBlock) {
        self.block = Some(block);
    }

    pub fn block(&self) -> BasicBlock {
        self.block.unwrap()
    }

    pub fn to_json(&self, repacker: PlaceRepacker<'mir, 'tcx>) -> Value {
        json!({
            "before_start": self.before_start.to_json(repacker),
            "before_after": self.before_after.to_json(repacker),
            "start": self.start.to_json(repacker),
            "after": self.after.to_json(repacker),
        })
    }

    pub fn new(
        repacker: PlaceRepacker<'mir, 'tcx>,
        output_facts: Rc<PoloniusOutput>,
        location_table: Rc<LocationTable>,
        block: Option<BasicBlock>,
    ) -> Self {
        Self {
            before_start: BorrowsState::new(),
            before_after: BorrowsState::new(),
            start: BorrowsState::new(),
            after: BorrowsState::new(),
            block,
            repacker,
            output_facts,
            location_table,
        }
    }

    pub fn initialize_as_start_block(&mut self) {
        for arg in self.repacker.body().args_iter() {
            if let ty::TyKind::Ref(region, _, mutability) =
                self.repacker.body().local_decls[arg].ty.kind()
            {
                let arg_place: Place<'tcx> = arg.into();
                self.after.add_reborrow(
                    MaybeRemotePlace::place_assigned_to_local(arg),
                    arg_place.project_deref(self.repacker),
                    *mutability,
                    Location::START,
                    *region,
                );
            }
        }
    }

    pub fn body(&self) -> &'mir Body<'tcx> {
        self.repacker.body()
    }
}
