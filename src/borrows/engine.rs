use std::default::Default;
use std::rc::Rc;

use serde_json::json;

use crate::{
    combined_pcs::{EvalStmtPhase, PCGError, PCGNodeLike},
    free_pcs::CapabilityKind,
    rustc_interface::{
        borrowck::{
            borrow_set::BorrowSet,
            consumers::{PoloniusOutput, RegionInferenceContext},
        },
        dataflow::{Analysis, AnalysisDomain, JoinSemiLattice},
        middle::{
            mir::{
                visit::Visitor, BasicBlock, Body, CallReturnPlaces, Local, Location, Statement,
                Terminator, TerminatorEdges,
            },
            ty::{self, TyCtxt},
        },
    },
    utils::{
        display::{DebugLines, DisplayDiff},
        validity::HasValidityCheck,
    },
};

use crate::{
    utils::{self, Place, PlaceRepacker},
    BorrowsBridge,
};

use super::{
    borrow_pcg_action::BorrowPCGAction,
    borrows_state::BorrowsState,
    borrows_visitor::{BorrowCheckerImpl, BorrowPCGActions, BorrowsVisitor, StatementStage},
    domain::{MaybeRemotePlace, RemotePlace, ToJsonWithRepacker},
    path_condition::{PathCondition, PathConditions},
    region_projection::RegionProjection,
    region_projection_member::{RegionProjectionMember, RegionProjectionMemberKind},
};

pub struct BorrowsEngine<'mir, 'tcx> {
    pub(crate) tcx: TyCtxt<'tcx>,
    pub(crate) body: &'mir Body<'tcx>,
    pub(crate) output_facts: Option<&'mir PoloniusOutput>,
}

impl<'mir, 'tcx> BorrowsEngine<'mir, 'tcx> {
    pub(crate) fn new(
        tcx: TyCtxt<'tcx>,
        body: &'mir Body<'tcx>,
        output_facts: Option<&'mir PoloniusOutput>,
    ) -> Self {
        BorrowsEngine {
            tcx,
            body,
            output_facts,
        }
    }
}

const DEBUG_JOIN_ITERATION_LIMIT: usize = 1000;

impl<'mir, 'tcx> JoinSemiLattice for BorrowsDomain<'mir, 'tcx> {
    fn join(&mut self, other: &Self) -> bool {
        if self.phase != DataflowPhase::Init {
            self.entry_state = self.states.post_main.clone();
            self.phase = DataflowPhase::Join;
        }
        self.debug_join_iteration += 1;

        if self.debug_join_iteration > DEBUG_JOIN_ITERATION_LIMIT {
            panic!(
                "Block {:?} has not terminated after {} join iterations, this is probably a bug",
                self.block(),
                self.debug_join_iteration
            );
        }
        if other.has_error() && !self.has_error() {
            self.error = other.error.clone();
            return true;
        } else if self.has_error() {
            return false;
        }
        // For performance reasons we don't check validity here.
        // if validity_checks_enabled() {
        //     debug_assert!(other.is_valid(), "Other graph is invalid");
        // }
        let mut other_after = other.post_main_state().clone();

        // For edges in the other graph that actually belong to it,
        // add the path condition that leads them to this block
        let pc = PathCondition::new(other.block(), self.block());
        other_after.add_path_condition(pc);

        let self_block = self.block();

        self.entry_state.join(
            &other_after,
            self_block,
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
        if location.statement_index == 0 {
            // The entry state may have taken into account previous joins
            state.states.post_main = state.entry_state.clone();
            state.phase = DataflowPhase::Transfer;
        } else {
            // This statement is not the first one in the block, so it's initial
            // state is the after_main state of the previous statement
            state.entry_state = state.states.post_main.clone();
        }
        state.states.pre_operands = state.states.post_main.clone();
        BorrowsVisitor::preparing(self, state, StatementStage::Operands)
            .visit_statement(statement, location);

        if !state.actions.pre_operands.is_empty() {
            state.states.pre_operands = state.states.post_main.clone();
        } else {
            if !state.has_error() {
                if state.states.pre_operands != state.entry_state {
                    panic!(
                        "{:?}: No actions were emitted, but the state has changed:\n{}",
                        location,
                        state.entry_state.fmt_diff(
                            &state.states.pre_operands,
                            PlaceRepacker::new(self.body, self.tcx)
                        )
                    );
                }
            }
        }
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
        if location.statement_index == 0 {
            // The entry state may have taken into account previous joins
            state.states.post_main = state.entry_state.clone();
            state.phase = DataflowPhase::Transfer;
        } else {
            // This statement is not the first one in the block, so it's initial
            // state is the after_main state of the previous statement
            state.entry_state = state.states.post_main.clone();
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
    pub fn map<U>(self, f: impl Fn(T) -> U) -> EvalStmtData<U> {
        EvalStmtData {
            pre_operands: f(self.pre_operands),
            post_operands: f(self.post_operands),
            pre_main: f(self.pre_main),
            post_main: f(self.post_main),
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = (EvalStmtPhase, &T)> {
        [
            (EvalStmtPhase::PreOperands, &self.pre_operands),
            (EvalStmtPhase::PostOperands, &self.post_operands),
            (EvalStmtPhase::PreMain, &self.pre_main),
            (EvalStmtPhase::PostMain, &self.post_main),
        ]
        .into_iter()
    }

    pub(crate) fn iter_mut(&mut self) -> impl Iterator<Item = (EvalStmtPhase, &mut T)> {
        [
            (EvalStmtPhase::PreOperands, &mut self.pre_operands),
            (EvalStmtPhase::PostOperands, &mut self.post_operands),
            (EvalStmtPhase::PreMain, &mut self.pre_main),
            (EvalStmtPhase::PostMain, &mut self.post_main),
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

impl<'tcx> HasValidityCheck<'tcx> for BorrowsStates<'tcx> {
    fn check_validity(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Result<(), String> {
        self.pre_operands.check_validity(repacker)?;
        self.post_operands.check_validity(repacker)?;
        self.pre_main.check_validity(repacker)?;
        self.post_main.check_validity(repacker)
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub(crate) enum DataflowPhase {
    Init,
    Join,
    Transfer,
}

#[derive(Clone)]
/// The domain of the Borrow PCG dataflow analysis. Note that this contains many
/// fields which serve as context (e.g. reference to a borrow-checker impl to
/// properly compute joins) but are not updated in the analysis itself.
pub struct BorrowsDomain<'mir, 'tcx> {
    /// The state before evaluating the statement. If this statement is not the first statement
    /// of a block, this is simply the post_main state of the previous block.
    pub(crate) entry_state: BorrowsState<'tcx>,
    pub(crate) states: BorrowsStates<'tcx>,
    pub(crate) block: Option<BasicBlock>,
    pub(crate) repacker: PlaceRepacker<'mir, 'tcx>,
    pub(crate) actions: EvalStmtData<BorrowPCGActions<'tcx>>,
    pub(crate) bc: BorrowCheckerImpl<'mir, 'tcx>,
    /// The number of times the join operation has been called, this is just
    /// used for debugging to identify if the dataflow analysis is not
    /// terminating.
    pub(crate) debug_join_iteration: usize,
    pub(crate) phase: DataflowPhase,
    error: Option<PCGError>,
}

impl<'mir, 'tcx> PartialEq for BorrowsDomain<'mir, 'tcx> {
    fn eq(&self, other: &Self) -> bool {
        self.entry_state == other.entry_state
            && self.states == other.states
            && self.block == other.block
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
    pub(crate) fn get_bridge(&self) -> (BorrowsBridge<'tcx>, BorrowsBridge<'tcx>) {
        (
            self.actions.pre_operands.clone().into(),
            self.actions.pre_main.clone().into(),
        )
    }
    pub(crate) fn post_main_state(&self) -> &BorrowsState<'tcx> {
        &self.states.post_main
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

    #[allow(unused)]
    pub(crate) fn has_internal_error(&self) -> bool {
        self.error
            .as_ref()
            .map_or(false, |e| matches!(e, PCGError::Internal(_)))
    }

    pub(crate) fn has_error(&self) -> bool {
        self.error.is_some()
    }

    pub(crate) fn new(
        repacker: PlaceRepacker<'mir, 'tcx>,
        region_inference_context: Rc<RegionInferenceContext<'tcx>>,
        borrow_set: Rc<BorrowSet<'tcx>>,
        block: Option<BasicBlock>,
    ) -> Self {
        Self {
            phase: DataflowPhase::Init,
            entry_state: BorrowsState::default(),
            states: BorrowsStates::default(),
            actions: EvalStmtData::default(),
            block,
            repacker,
            debug_join_iteration: 0,
            error: None,
            bc: BorrowCheckerImpl::new(repacker, region_inference_context, borrow_set),
        }
    }

    fn introduce_initial_borrows(&mut self, local: Local) {
        let local_decl = &self.repacker.body().local_decls[local];
        let arg_place: Place<'tcx> = local.into();
        if let ty::TyKind::Ref(region, _, mutability) = local_decl.ty.kind() {
            assert!(self.entry_state.set_capability(
                MaybeRemotePlace::place_assigned_to_local(local),
                if mutability.is_mut() {
                    CapabilityKind::Exclusive
                } else {
                    CapabilityKind::Read
                },
            ));
            let _ = self.entry_state.apply_action(
                BorrowPCGAction::add_region_projection_member(
                    RegionProjectionMember::new(
                        vec![MaybeRemotePlace::place_assigned_to_local(local).into()],
                        vec![
                            RegionProjection::new((*region).into(), arg_place, self.repacker)
                                .into(),
                        ],
                        RegionProjectionMemberKind::FunctionInput,
                    ),
                    PathConditions::AtBlock((Location::START).block),
                    "Introduce initial borrow",
                ),
                self.repacker,
            );
        }
        let local_place: utils::Place<'tcx> = arg_place.into();
        for region_projection in local_place.region_projections(self.repacker) {
            assert!(self.entry_state.apply_action(
                BorrowPCGAction::add_region_projection_member(
                    RegionProjectionMember::new(
                        vec![RegionProjection::new(
                            region_projection.region(self.repacker),
                            RemotePlace::new(local),
                            self.repacker,
                        )
                        .to_pcg_node(),],
                        vec![region_projection.into()],
                        RegionProjectionMemberKind::Todo,
                    ),
                    PathConditions::AtBlock((Location::START).block),
                    "Initialize Local",
                ),
                self.repacker,
            ));
        }
    }

    pub(crate) fn initialize_as_start_block(&mut self) {
        for arg in self.repacker.body().args_iter() {
            let arg_place: utils::Place<'tcx> = arg.into();
            for rp in arg_place.region_projections(self.repacker) {
                assert!(self
                    .entry_state
                    .set_capability(rp, CapabilityKind::Exclusive));
            }
            self.introduce_initial_borrows(arg);
        }
    }
}
