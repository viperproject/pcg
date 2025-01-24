use std::default::Default;
use std::rc::Rc;

use serde_json::json;

use crate::{
    combined_pcs::{EvalStmtPhase, PCGError},
    rustc_interface::{
        borrowck::{
            borrow_set::BorrowSet,
            consumers::{LocationTable, PoloniusInput, PoloniusOutput, RegionInferenceContext},
        },
        dataflow::{
            impls::MaybeLiveLocals, Analysis, AnalysisDomain, JoinSemiLattice, Results,
            ResultsCursor,
        },
        middle::{
            mir::{
                visit::Visitor, BasicBlock, Body, CallReturnPlaces, Local, Location, Statement,
                Terminator, TerminatorEdges,
            },
            ty::{self, TyCtxt},
        },
    },
};

use crate::{
    utils::{self, Place, PlaceRepacker},
    BorrowsBridge,
};

use super::{
    borrow_pcg_action::BorrowPCGAction,
    borrow_pcg_edge::PCGNode,
    borrows_state::BorrowsState,
    borrows_visitor::{BorrowCheckerImpl, BorrowsVisitor, DebugCtx, StatementStage},
    coupling_graph_constructor::{BorrowCheckerInterface, CGNode, Coupled},
    domain::{MaybeRemotePlace, RemotePlace, ToJsonWithRepacker},
    path_condition::{PathCondition, PathConditions},
    region_projection::RegionProjection,
    region_projection_member::RegionProjectionMember,
};

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
        let mut other_after = other.post_state().clone();

        // For edges in the other graph that actually belong to it,
        // add the path condition that leads them to this block
        let pc = PathCondition::new(other.block(), self.block());
        other_after.add_path_condition(pc);

        // Overlay both graphs
        self.states.post_main.join(
            &other_after,
            self.block(),
            other.block(),
            &self.bc,
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
        state.states.pre_operands = state.states.post_main.clone();
        BorrowsVisitor::applying(self, state, StatementStage::Operands)
            .visit_statement(statement, location);
        state.states.post_operands = state.states.post_main.clone();
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
        state.states.pre_main = state.states.post_main.clone();
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
        state.states.pre_operands = state.states.post_main.clone();
        BorrowsVisitor::applying(self, state, StatementStage::Operands)
            .visit_terminator(terminator, location);
        state.states.post_operands = state.states.post_main.clone();
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
        state.states.pre_main = state.states.post_main.clone();
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
pub struct EvalStmtData<T> {
    pub(crate) pre_operands: T,
    pub(crate) post_operands: T,
    pub(crate) pre_main: T,
    pub(crate) post_main: T,
}

impl<'tcx, T: ToJsonWithRepacker<'tcx>> ToJsonWithRepacker<'tcx> for EvalStmtData<T> {
    fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        json!({
            "pre_operands": self.pre_operands.to_json(repacker),
            "post_operands": self.post_operands.to_json(repacker),
            "pre_main": self.pre_main.to_json(repacker),
            "post_main": self.post_main.to_json(repacker),
        })
    }
}

impl<T: Default> Default for EvalStmtData<T> {
    fn default() -> Self {
        Self {
            pre_operands: T::default(),
            post_operands: T::default(),
            pre_main: T::default(),
            post_main: T::default(),
        }
    }
}

impl<T> EvalStmtData<T> {
    pub fn iter(&self) -> impl Iterator<Item = (EvalStmtPhase, &T)> {
        [
            (EvalStmtPhase::PreOperands, &self.pre_operands),
            (EvalStmtPhase::PostOperands, &self.post_operands),
            (EvalStmtPhase::PreMain, &self.pre_main),
            (EvalStmtPhase::PostMain, &self.post_main),
        ]
        .into_iter()
    }
    pub(crate) fn get(&self, phase: EvalStmtPhase) -> &T {
        match phase {
            EvalStmtPhase::PreOperands => &self.pre_operands,
            EvalStmtPhase::PostOperands => &self.post_operands,
            EvalStmtPhase::PreMain => &self.pre_main,
            EvalStmtPhase::PostMain => &self.post_main,
        }
    }
    pub fn post_main(&self) -> &T {
        &self.post_main
    }
}

impl<T> std::ops::Index<EvalStmtPhase> for EvalStmtData<T> {
    type Output = T;

    fn index(&self, phase: EvalStmtPhase) -> &Self::Output {
        self.get(phase)
    }
}

impl<T> std::ops::IndexMut<EvalStmtPhase> for EvalStmtData<T> {
    fn index_mut(&mut self, phase: EvalStmtPhase) -> &mut Self::Output {
        match phase {
            EvalStmtPhase::PreOperands => &mut self.pre_operands,
            EvalStmtPhase::PostOperands => &mut self.post_operands,
            EvalStmtPhase::PreMain => &mut self.pre_main,
            EvalStmtPhase::PostMain => &mut self.post_main,
        }
    }
}

pub(crate) type BorrowsStates<'tcx> = EvalStmtData<BorrowsState<'tcx>>;

impl<'tcx> BorrowsStates<'tcx> {
    pub(crate) fn bridge_between_stmts(
        &self,
        next: &BorrowsStates<'tcx>,
        debug_ctx: DebugCtx,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> (BorrowsBridge<'tcx>, BorrowsBridge<'tcx>) {
        let start = self
            .post_main
            .bridge(&next.pre_operands, debug_ctx, repacker);
        let middle = next
            .post_operands
            .bridge(&next.pre_main, debug_ctx, repacker);
        (start, middle)
    }
}
#[derive(Clone)]
pub struct BorrowsDomain<'mir, 'tcx> {
    pub(crate) states: BorrowsStates<'tcx>,
    pub(crate) block: Option<BasicBlock>,
    pub(crate) repacker: PlaceRepacker<'mir, 'tcx>,
    #[allow(unused)]
    pub(crate) output_facts: Rc<PoloniusOutput>,
    #[allow(unused)]
    pub(crate) location_table: Rc<LocationTable>,
    pub(crate) actions: EvalStmtData<Vec<BorrowPCGAction<'tcx>>>,
    pub(crate) bc: BorrowCheckerImpl<'mir, 'tcx>,
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
            .field("states", &self.states)
            .field("block", &self.block)
            .finish()
    }
}

impl<'mir, 'tcx> BorrowsDomain<'mir, 'tcx> {
    pub(crate) fn post_state(&self) -> &BorrowsState<'tcx> {
        &self.states.post_main
    }

    pub(crate) fn is_valid(&self) -> bool {
        self.post_state().is_valid(self.repacker)
    }

    pub(crate) fn post_state_mut(&mut self) -> &mut BorrowsState<'tcx> {
        &mut self.states.post_main
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
        region_inference_context: Rc<RegionInferenceContext<'tcx>>,
        block: Option<BasicBlock>,
    ) -> Self {
        Self {
            states: BorrowsStates::default(),
            actions: EvalStmtData::default(),
            block,
            repacker,
            output_facts,
            location_table,
            error: None,
            bc: BorrowCheckerImpl::new(&repacker, region_inference_context),
        }
    }

    pub(super) fn introduce_initial_borrows(&mut self, local: Local, location: Location) {
        let local_decl = &self.repacker.body().local_decls[local];
        let arg_place: Place<'tcx> = local.into();
        if let ty::TyKind::Ref(region, _, mutability) = local_decl.ty.kind() {
            let _ = self.states.post_main.add_borrow(
                MaybeRemotePlace::place_assigned_to_local(local),
                arg_place.project_deref(self.repacker),
                *mutability,
                location,
                *region,
                self.repacker,
            );
        }
        let local_place: utils::Place<'tcx> = arg_place.into();
        for region_projection in local_place.region_projections(self.repacker) {
            self.states.post_main.apply_action(
                BorrowPCGAction::add_region_projection_member(
                    RegionProjectionMember::new(
                        Coupled::singleton(
                            RegionProjection::new(
                                region_projection.region(),
                                RemotePlace::new(local),
                            )
                            .into(),
                        ),
                        Coupled::singleton(region_projection.into()),
                    ),
                    PathConditions::AtBlock(location.block),
                    "Initialize Local",
                ),
                self.repacker,
            );
        }
    }

    pub(crate) fn initialize_as_start_block(&mut self) {
        for arg in self.repacker.body().args_iter() {
            self.introduce_initial_borrows(arg, Location::START);
        }
    }
}
