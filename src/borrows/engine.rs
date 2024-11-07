use std::rc::Rc;

use rustc_interface::{
    borrowck::{
        borrow_set::BorrowSet,
        consumers::{LocationTable, PoloniusInput, PoloniusOutput, RegionInferenceContext},
    },
    dataflow::{impls::MaybeLiveLocals, Analysis, AnalysisDomain, JoinSemiLattice, Results},
    middle::{
        mir::{
            visit::Visitor, BasicBlock, Body, CallReturnPlaces, Location, Statement,
            Terminator, TerminatorEdges,
        },
        ty::{self, TyCtxt},
    },
};
use serde_json::{json, Value};

use crate::{
    borrows::domain::ToJsonWithRepacker,
    rustc_interface,
    utils::{self, Place, PlaceRepacker},
    BorrowsBridge,
};

use super::{
    borrow_edge::BorrowEdge, borrows_state::BorrowsState, borrows_visitor::{BorrowsVisitor, DebugCtx, StatementStage}, coupling_graph_constructor::LivenessChecker, domain::MaybeRemotePlace, path_condition::PathCondition, region_projection::RegionProjection
};
use super::{
    deref_expansion::DerefExpansion,
    domain::{MaybeOldPlace},
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
    AddReborrow(BorrowEdge<'tcx>),
    RemoveReborrow(BorrowEdge<'tcx>),
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

impl<'tcx> LivenessChecker<'tcx> for Results<'tcx, MaybeLiveLocals> {
    fn is_live(&self, region_projection: RegionProjection<'tcx>, block: BasicBlock) -> bool {
        self.entry_set_for_block(block)
            .contains(region_projection.local())
    }
}

impl<'mir, 'tcx> JoinSemiLattice for BorrowsDomain<'mir, 'tcx> {
    fn join(&mut self, other: &Self) -> bool {
        let mut other_after = other.after_state().clone();

        // For edges in the other graph that actually belong to it,
        // add the path condition that leads them to this block
        let pc = PathCondition::new(other.block(), self.block());
        other_after.add_path_condition(pc);

        // Overlay both graphs
        self.states.after.join(
            &other_after,
            self.block(),
            other.block(),
            self.maybe_live_locals.as_ref(),
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
        BorrowsVisitor::preparing(self, state, StatementStage::Operands)
            .visit_statement(statement, location);
        state.states.before_start = state.states.after.clone();
        BorrowsVisitor::applying(self, state, StatementStage::Operands)
            .visit_statement(statement, location);
        state.states.before_after = state.states.after.clone();
    }

    fn apply_statement_effect(
        &mut self,
        state: &mut BorrowsDomain<'a, 'tcx>,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        BorrowsVisitor::preparing(self, state, StatementStage::Main)
            .visit_statement(statement, location);
        state.states.start = state.states.after.clone();
        BorrowsVisitor::applying(self, state, StatementStage::Main)
            .visit_statement(statement, location);
    }

    fn apply_before_terminator_effect(
        &mut self,
        state: &mut BorrowsDomain<'a, 'tcx>,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) {
        BorrowsVisitor::preparing(self, state, StatementStage::Operands)
            .visit_terminator(terminator, location);
        state.states.before_start = state.states.after.clone();
        BorrowsVisitor::applying(self, state, StatementStage::Operands)
            .visit_terminator(terminator, location);
        state.states.before_after = state.states.after.clone();
    }

    fn apply_terminator_effect<'mir>(
        &mut self,
        state: &mut BorrowsDomain<'a, 'tcx>,
        terminator: &'mir Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        BorrowsVisitor::preparing(self, state, StatementStage::Main)
            .visit_terminator(terminator, location);
        state.states.start = state.states.after.clone();
        BorrowsVisitor::applying(self, state, StatementStage::Main)
            .visit_terminator(terminator, location);
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

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct BorrowsStates<'tcx> {
    pub before_start: BorrowsState<'tcx>,
    pub before_after: BorrowsState<'tcx>,
    pub start: BorrowsState<'tcx>,
    pub after: BorrowsState<'tcx>,
}

impl<'tcx> BorrowsStates<'tcx> {
    pub fn new() -> Self {
        Self {
            before_start: BorrowsState::new(),
            before_after: BorrowsState::new(),
            start: BorrowsState::new(),
            after: BorrowsState::new(),
        }
    }

    pub fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Value {
        json!({
            "before_start": self.before_start.to_json(repacker),
            "before_after": self.before_after.to_json(repacker),
            "start": self.start.to_json(repacker),
            "after": self.after.to_json(repacker),
        })
    }

    pub fn bridge_between_stmts(
        &self,
        next: &BorrowsStates<'tcx>,
        debug_ctx: DebugCtx,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> (BorrowsBridge<'tcx>, BorrowsBridge<'tcx>) {
        let start = self.after.bridge(&next.before_start, debug_ctx, repacker);
        let middle = next.before_after.bridge(&next.start, debug_ctx, repacker);
        (start, middle)
    }
}
#[derive(Clone)]
pub struct BorrowsDomain<'mir, 'tcx> {
    pub states: BorrowsStates<'tcx>,
    pub block: Option<BasicBlock>,
    pub repacker: PlaceRepacker<'mir, 'tcx>,
    pub output_facts: Rc<PoloniusOutput>,
    pub location_table: Rc<LocationTable>,
    pub maybe_live_locals: Rc<Results<'tcx, MaybeLiveLocals>>,
}

impl<'mir, 'tcx> PartialEq for BorrowsDomain<'mir, 'tcx> {
    fn eq(&self, other: &Self) -> bool {
        self.states == other.states && self.block == other.block
    }
}

impl<'mir, 'tcx> Eq for BorrowsDomain<'mir, 'tcx> {}

impl<'mir, 'tcx> std::fmt::Debug for BorrowsDomain<'mir, 'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BorrowsDomain")
            .field("before_start", &self.states.before_start)
            .field("before_after", &self.states.before_after)
            .field("start", &self.states.start)
            .field("after", &self.states.after)
            .field("block", &self.block)
            .finish()
    }
}

impl<'mir, 'tcx> BorrowsDomain<'mir, 'tcx> {
    pub fn after_state(&self) -> &BorrowsState<'tcx> {
        &self.states.after
    }

    pub fn after_state_mut(&mut self) -> &mut BorrowsState<'tcx> {
        &mut self.states.after
    }

    pub fn is_initialized(&self) -> bool {
        self.block.is_some()
    }

    pub fn set_block(&mut self, block: BasicBlock) {
        self.block = Some(block);
    }

    pub fn block(&self) -> BasicBlock {
        self.block.unwrap()
    }

    pub fn new(
        repacker: PlaceRepacker<'mir, 'tcx>,
        output_facts: Rc<PoloniusOutput>,
        location_table: Rc<LocationTable>,
        block: Option<BasicBlock>,
        maybe_live_locals: Rc<Results<'tcx, MaybeLiveLocals>>,
    ) -> Self {
        Self {
            states: BorrowsStates::new(),
            block,
            repacker,
            output_facts,
            location_table,
            maybe_live_locals,
        }
    }

    pub fn initialize_as_start_block(&mut self) {
        for arg in self.repacker.body().args_iter() {
            if let ty::TyKind::Ref(region, _, mutability) =
                self.repacker.body().local_decls[arg].ty.kind()
            {
                let arg_place: Place<'tcx> = arg.into();
                self.states.after.add_borrow(
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
