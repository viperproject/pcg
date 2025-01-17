use std::rc::Rc;

use crate::{
    combined_pcs::PCGError,
    rustc_interface::{
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
    },
};
use serde_json::{json, Value};

use crate::{
    borrows::domain::ToJsonWithRepacker,
    utils::{self, Place, PlaceRepacker},
    BorrowsBridge,
};

use super::{
    borrow_edge::BorrowEdge,
    borrows_state::BorrowsState,
    borrows_visitor::{BorrowsVisitor, DebugCtx, StatementStage},
    coupling_graph_constructor::{BorrowCheckerInterface, CGNode, Coupled},
    domain::{MaybeRemotePlace, RemotePlace},
    path_condition::{PathCondition, PathConditions},
    region_projection::RegionProjection,
    region_projection_member::RegionProjectionMember,
};
use super::{deref_expansion::DerefExpansion, domain::MaybeOldPlace};

pub struct BorrowsEngine<'mir, 'tcx> {
    pub(crate) tcx: TyCtxt<'tcx>,
    pub(crate) body: &'mir Body<'tcx>,
    pub(crate) location_table: &'mir LocationTable,
    pub(crate) input_facts: &'mir PoloniusInput,
    pub(crate) borrow_set: Rc<BorrowSet<'tcx>>,
    pub(crate) region_inference_context: Rc<RegionInferenceContext<'tcx>>,
    pub(crate) output_facts: &'mir PoloniusOutput,
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

impl<'tcx> BorrowCheckerInterface<'tcx> for Results<'tcx, MaybeLiveLocals> {
    fn is_live(&self, node: CGNode<'tcx>, block: BasicBlock) -> bool {
        match node {
            CGNode::RegionProjection(rp) => {
                if let Some(local) = rp.local() {
                    self.entry_set_for_block(block).contains(local)
                } else {
                    todo!()
                }
            }
            CGNode::RemotePlace(_) => true,
        }
    }
}

impl<'mir, 'tcx> JoinSemiLattice for BorrowsDomain<'mir, 'tcx> {
    fn join(&mut self, other: &Self) -> bool {
        if other.has_error() && !self.has_error() {
            self.error = other.error.clone();
            return true;
        } else if self.has_error() {
            return false;
        }
        if self.repacker.should_check_validity() {
            debug_assert!(other.is_valid(), "Other graph is invalid");
        }
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
        if state.has_error() {
            return;
        }
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
        if state.has_error() {
            return;
        }
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
        if state.has_error() {
            return;
        }
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
        if state.has_error() {
            return terminator.edges();
        }
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
    pub(crate) states: BorrowsStates<'tcx>,
    pub(crate) block: Option<BasicBlock>,
    pub(crate) repacker: PlaceRepacker<'mir, 'tcx>,
    pub(crate) output_facts: Rc<PoloniusOutput>,
    pub(crate) location_table: Rc<LocationTable>,
    pub(crate) maybe_live_locals: Rc<Results<'tcx, MaybeLiveLocals>>,
    error: Option<PCGError>,
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
    pub(crate) fn error(&self) -> Option<&PCGError> {
        self.error.as_ref()
    }
    pub(crate) fn is_valid(&self) -> bool {
        self.states.after.is_valid(self.repacker)
    }
    pub(crate) fn after_state(&self) -> &BorrowsState<'tcx> {
        &self.states.after
    }

    pub(crate) fn after_state_mut(&mut self) -> &mut BorrowsState<'tcx> {
        &mut self.states.after
    }

    pub(crate) fn set_block(&mut self, block: BasicBlock) {
        self.block = Some(block);
    }

    pub(crate) fn block(&self) -> BasicBlock {
        self.block.unwrap()
    }

    pub(crate) fn report_error(&mut self, error: PCGError) {
        eprintln!("PCG Error: {:?}", error);
        self.error = Some(error);
    }

    pub(crate) fn has_error(&self) -> bool {
        self.error.is_some()
    }

    pub(crate) fn new(
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
            error: None,
        }
    }

    pub(crate) fn initialize_as_start_block(&mut self) {
        for arg in self.repacker.body().args_iter() {
            let local_decl = &self.repacker.body().local_decls[arg];
            let arg_place: Place<'tcx> = arg.into();
            if let ty::TyKind::Ref(region, _, mutability) = local_decl.ty.kind() {
                {
                    self.states.after.add_borrow(
                        MaybeRemotePlace::place_assigned_to_local(arg),
                        arg_place.project_deref(self.repacker),
                        *mutability,
                        Location::START,
                        *region,
                        self.repacker,
                    );
                }
            }
            let local_place: utils::Place<'tcx> = arg_place.into();
            for region_projection in local_place.region_projections(self.repacker) {
                self.states.after.add_region_projection_member(
                    RegionProjectionMember::new(
                        Coupled::singleton(
                            RegionProjection::new(
                                region_projection.region(),
                                RemotePlace::new(arg),
                            )
                            .into(),
                        ),
                        Coupled::singleton(region_projection.into()),
                    ),
                    PathConditions::start(),
                    self.repacker,
                );
            }
        }
    }
}
