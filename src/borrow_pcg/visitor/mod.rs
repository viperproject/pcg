use crate::combined_pcs::EvalStmtPhase::*;
use tracing::instrument;

use crate::{
    combined_pcs::{PCGError, PCGUnsupportedError},
    rustc_interface::{
        borrowck::PoloniusOutput,
        index::IndexVec,
        middle::{
            mir::{
                self,
                visit::{PlaceContext, Visitor},
                BorrowKind, Const, Location, Operand, Rvalue, Statement, StatementKind, Terminator,
                TerminatorKind,
            },
            ty::{self, TypeVisitable, TypeVisitor},
        },
    },
    utils::Place,
};

use super::{
    action::BorrowPCGAction,
    borrow_pcg_edge::BorrowPCGEdge,
    coupling_graph_constructor::BorrowCheckerInterface,
    edge::outlives::{OutlivesEdge, OutlivesEdgeKind},
    path_condition::PathConditions,
    region_projection::{PCGRegion, RegionIdx, RegionProjection},
};
use super::{domain::AbstractionOutputTarget, engine::BorrowsEngine};
use crate::borrow_pcg::action::actions::BorrowPCGActions;
use crate::borrow_pcg::action::executed_actions::ExecutedActions;
use crate::borrow_pcg::domain::BorrowsDomain;
use crate::borrow_pcg::edge::abstraction::{
    AbstractionBlockEdge, AbstractionType, FunctionCallAbstraction,
};
use crate::borrow_pcg::state::obtain::ObtainReason;
use crate::utils::place::maybe_old::MaybeOldPlace;
use crate::{
    free_pcs::CapabilityKind,
    utils::{self, PlaceRepacker, PlaceSnapshot},
};

mod stmt;

#[derive(Debug, Clone, Copy)]
pub(crate) enum DebugCtx {
    #[allow(unused)]
    Location(Location),
    #[allow(unused)]
    Other,
}

impl DebugCtx {
    pub(crate) fn new(location: Location) -> DebugCtx {
        DebugCtx::Location(location)
    }

    #[allow(unused)]
    pub(crate) fn location(&self) -> Option<Location> {
        match self {
            DebugCtx::Location(location) => Some(*location),
            DebugCtx::Other => None,
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub(crate) enum StatementStage {
    Operands,
    Main,
}

pub(crate) struct BorrowsVisitor<'tcx, 'mir, 'state> {
    pub(super) repacker: PlaceRepacker<'mir, 'tcx>,
    pub(super) domain: &'state mut BorrowsDomain<'mir, 'tcx>,
    stage: StatementStage,
    preparing: bool,
    debug_ctx: Option<DebugCtx>,
    #[allow(dead_code)]
    output_facts: Option<&'mir PoloniusOutput>,
}

impl<'tcx, 'mir, 'state> BorrowsVisitor<'tcx, 'mir, 'state> {
    fn curr_actions(&mut self) -> &mut BorrowPCGActions<'tcx> {
        match (self.stage, self.preparing) {
            (StatementStage::Operands, true) => &mut self.domain.actions.pre_operands,
            (StatementStage::Operands, false) => &mut self.domain.actions.post_operands,
            (StatementStage::Main, true) => &mut self.domain.actions.pre_main,
            (StatementStage::Main, false) => &mut self.domain.actions.post_main,
        }
    }

    fn reset_actions(&mut self) {
        self.curr_actions().clear();
    }

    fn record_actions(&mut self, actions: ExecutedActions<'tcx>) {
        self.curr_actions().extend(actions.actions());
    }

    fn apply_action(&mut self, action: BorrowPCGAction<'tcx>) -> bool {
        self.curr_actions().push(action.clone());
        self.domain
            .post_state_mut()
            .apply_action(action, self.repacker)
            .unwrap()
    }

    pub(super) fn preparing(
        engine: &BorrowsEngine<'mir, 'tcx>,
        state: &'state mut BorrowsDomain<'mir, 'tcx>,
        stage: StatementStage,
    ) -> BorrowsVisitor<'tcx, 'mir, 'state> {
        let mut bv = BorrowsVisitor::new(engine, state, stage, true);
        bv.reset_actions();
        bv
    }

    pub(super) fn applying(
        engine: &BorrowsEngine<'mir, 'tcx>,
        state: &'state mut BorrowsDomain<'mir, 'tcx>,
        stage: StatementStage,
    ) -> BorrowsVisitor<'tcx, 'mir, 'state> {
        let mut bv = BorrowsVisitor::new(engine, state, stage, false);
        bv.reset_actions();
        bv
    }

    fn new(
        engine: &BorrowsEngine<'mir, 'tcx>,
        state: &'state mut BorrowsDomain<'mir, 'tcx>,
        stage: StatementStage,
        preparing: bool,
    ) -> BorrowsVisitor<'tcx, 'mir, 'state> {
        BorrowsVisitor {
            repacker: PlaceRepacker::new(engine.body, engine.tcx),
            domain: state,
            stage,
            preparing,
            debug_ctx: None,
            output_facts: engine.output_facts,
        }
    }

    fn connect_outliving_projections(
        &mut self,
        source_proj: RegionProjection<'tcx, MaybeOldPlace<'tcx>>,
        target: Place<'tcx>,
        location: Location,
        kind: impl Fn(PCGRegion) -> OutlivesEdgeKind,
    ) {
        for target_proj in target.region_projections(self.repacker).into_iter() {
            if self.outlives(
                source_proj.region(self.repacker),
                target_proj.region(self.repacker),
            ) {
                self.apply_action(BorrowPCGAction::add_edge(
                    BorrowPCGEdge::new(
                        OutlivesEdge::new(
                            source_proj.into(),
                            target_proj.into(),
                            kind(target_proj.region(self.repacker)),
                            self.repacker,
                        )
                        .into(),
                        PathConditions::AtBlock(location.block),
                    ),
                    true,
                ));
            }
        }
    }

    fn outlives(&self, sup: PCGRegion, sub: PCGRegion) -> bool {
        self.domain.bc.outlives(sup, sub)
    }

    /// Constructs a function call abstraction, if necessary.
    fn construct_function_call_abstraction(
        &mut self,
        func: &Operand<'tcx>,
        args: &[&Operand<'tcx>],
        destination: utils::Place<'tcx>,
        location: Location,
    ) {
        // This is just a performance optimization
        if self
            .domain
            .post_main_state()
            .graph()
            .has_function_call_abstraction_at(location)
        {
            return;
        }
        let (func_def_id, substs) = if let Operand::Constant(box c) = func
            && let Const::Val(_, ty) = c.const_
            && let ty::TyKind::FnDef(def_id, substs) = ty.kind()
        {
            (def_id, substs)
        } else {
            self.domain
                .report_error(PCGError::unsupported(PCGUnsupportedError::Other(format!(
                    "This type of function call is not yet supported: {:?}",
                    func
                ))));
            return;
        };
        let sig = self
            .repacker
            .tcx()
            .fn_sig(func_def_id)
            .instantiate(self.repacker.tcx(), substs);
        let sig = self
            .repacker
            .tcx()
            .liberate_late_bound_regions(*func_def_id, sig);

        // This is also a performance optimization
        let output_lifetimes = extract_regions(sig.output());
        if output_lifetimes.is_empty() {
            return;
        }

        for arg in args.iter() {
            let input_place: utils::Place<'tcx> = match arg.place() {
                Some(place) => place.into(),
                None => continue,
            };
            let input_place = MaybeOldPlace::OldPlace(PlaceSnapshot::new(
                input_place,
                self.domain.post_main_state().get_latest(input_place),
            ));
            let ty = input_place.ty(self.repacker).ty;
            for (lifetime_idx, input_lifetime) in extract_regions(ty).into_iter().enumerate() {
                for output in
                    self.projections_borrowing_from_input_lifetime(input_lifetime, destination)
                {
                    if let ty::TyKind::Closure(..) = ty.kind() {
                        self.domain.report_error(PCGError::unsupported(
                            PCGUnsupportedError::ClosuresCapturingBorrows,
                        ));
                        return;
                    }
                    let input_rp = input_place.region_projection(lifetime_idx, self.repacker);

                    let block_edge = AbstractionBlockEdge::new(
                        vec![input_rp.into()].into_iter().collect(),
                        vec![output].into_iter().collect(),
                    );
                    self.apply_action(BorrowPCGAction::add_edge(
                        BorrowPCGEdge::new(
                            AbstractionType::FunctionCall(FunctionCallAbstraction::new(
                                location,
                                *func_def_id,
                                substs,
                                block_edge,
                            ))
                            .into(),
                            PathConditions::AtBlock(location.block),
                        ),
                        true,
                    ));
                }
            }
        }
    }

    fn projections_borrowing_from_input_lifetime(
        &self,
        input_lifetime: PCGRegion,
        output_place: utils::Place<'tcx>,
    ) -> Vec<AbstractionOutputTarget<'tcx>> {
        let mut result = vec![];
        let output_ty = output_place.ty(self.repacker).ty;
        for (output_lifetime_idx, output_lifetime) in
            extract_regions(output_ty).into_iter_enumerated()
        {
            if self.outlives(input_lifetime, output_lifetime) {
                result.push(
                    output_place
                        .region_projection(output_lifetime_idx, self.repacker)
                        .into(),
                );
            }
        }
        result
    }
}

impl<'tcx> Visitor<'tcx> for BorrowsVisitor<'tcx, '_, '_> {
    fn visit_operand(&mut self, operand: &Operand<'tcx>, location: Location) {
        self.super_operand(operand, location);
        if self.domain.has_error() {
            return;
        }
        if self.stage == StatementStage::Operands && self.preparing {
            match operand {
                Operand::Copy(place) | Operand::Move(place) => {
                    let expansion_reason = if matches!(operand, Operand::Copy(..)) {
                        ObtainReason::CopyOperand
                    } else {
                        ObtainReason::MoveOperand
                    };
                    let place: utils::Place<'tcx> = (*place).into();
                    let expansion_actions = self.domain.post_state_mut().obtain(
                        self.repacker,
                        place,
                        location,
                        expansion_reason,
                    );
                    match expansion_actions {
                        Ok(actions) => {
                            self.record_actions(actions);
                        }
                        Err(e) => {
                            self.domain.report_error(e);
                        }
                    }
                }
                _ => {}
            }
        } else if self.stage == StatementStage::Operands && !self.preparing {
            if let Operand::Move(place) = operand {
                let place: utils::Place<'tcx> = (*place).into();
                if !place.is_owned(self.repacker) {
                    self.domain.post_state_mut().set_capability(
                        place.into(),
                        CapabilityKind::Write,
                        self.repacker,
                    );
                }
            }
        } else if self.stage == StatementStage::Main && !self.preparing {
            if let Operand::Move(place) = operand {
                let place: utils::Place<'tcx> = (*place).into();
                self.apply_action(BorrowPCGAction::make_place_old(place));
            }
        }
    }

    #[tracing::instrument(skip(self, terminator), fields(join_iteration = ?self.domain.debug_join_iteration))]
    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        if self.preparing && self.stage == StatementStage::Operands {
            let post_state = self.domain.data.states.get_mut(PostMain);
            let actions =
                post_state.pack_old_and_dead_leaves(self.repacker, location, &self.domain.bc);
            match actions {
                Ok(actions) => {
                    self.record_actions(actions);
                }
                Err(e) => {
                    self.domain.report_error(e);
                }
            }
        }
        self.super_terminator(terminator, location);
        if self.stage == StatementStage::Main && !self.preparing {
            if let TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } = &terminator.kind
            {
                let destination: utils::Place<'tcx> = (*destination).into();
                self.apply_action(BorrowPCGAction::set_latest(
                    destination,
                    location,
                    "Destination of Function Call",
                ));
                self.construct_function_call_abstraction(
                    func,
                    &args.iter().map(|arg| &arg.node).collect::<Vec<_>>(),
                    destination,
                    location,
                );
            }
        }
    }

    #[tracing::instrument(skip(self), fields(join_iteration = ?self.domain.debug_join_iteration))]
    fn visit_statement(&mut self, statement: &Statement<'tcx>, location: Location) {
        self.debug_ctx = Some(DebugCtx::new(location));

        if self.preparing && self.stage == StatementStage::Operands {
            // Remove places that are non longer live based on borrow checker information
            let actions = self
                .domain
                .data
                .states
                .get_mut(PostMain)
                .pack_old_and_dead_leaves(self.repacker, location, &self.domain.bc);
            match actions {
                Ok(actions) => {
                    self.record_actions(actions);
                }
                Err(e) => {
                    self.domain.report_error(e);
                }
            }
        }

        self.super_statement(statement, location);

        if self.preparing && self.stage == StatementStage::Operands {
            match &statement.kind {
                StatementKind::Assign(box (_, Rvalue::Cast(_, _, ty))) => {
                    if ty.ref_mutability().is_some() {
                        self.domain
                            .report_error(PCGError::unsupported(PCGUnsupportedError::CastToRef));
                        return;
                    } else if ty.is_unsafe_ptr() {
                        self.domain.report_error(PCGError::unsupported(
                            PCGUnsupportedError::UnsafePtrCast,
                        ));
                        return;
                    }
                }

                StatementKind::FakeRead(box (_, place)) => {
                    let place: utils::Place<'tcx> = (*place).into();
                    if !place.is_owned(self.repacker) {
                        let expansion_reason = ObtainReason::FakeRead;
                        let expansion_actions = self.domain.post_state_mut().obtain(
                            self.repacker,
                            place,
                            location,
                            expansion_reason,
                        );
                        match expansion_actions {
                            Ok(actions) => {
                                self.record_actions(actions);
                            }
                            Err(e) => {
                                self.domain.report_error(e);
                            }
                        }
                    }
                }
                _ => {}
            }
        } else if self.preparing && self.stage == StatementStage::Main {
            self.stmt_pre_main(statement, location);
        } else if !self.preparing && self.stage == StatementStage::Main {
            self.stmt_post_main(statement, location);
        }
    }

    fn visit_place(&mut self, place: &mir::Place<'tcx>, context: PlaceContext, location: Location) {
        {
            let place: utils::Place<'tcx> = (*place).into();
            if place.contains_unsafe_deref(self.repacker) {
                self.domain
                    .report_error(PCGError::unsupported(PCGUnsupportedError::DerefUnsafePtr));
                return;
            }
        }
        self.super_place(place, context, location);
    }

    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
        #[instrument(skip(this), fields(location = ?location))]
        fn visit_rvalue_inner<'tcx, 'mir, 'state>(
            this: &mut BorrowsVisitor<'tcx, 'mir, 'state>,
            rvalue: &Rvalue<'tcx>,
            location: Location,
        ) {
            if matches!(rvalue, Rvalue::Ref(_, BorrowKind::Fake(_), _)) {
                return;
            }
            this.super_rvalue(rvalue, location);
            if this.domain.has_error() {
                return;
            }
            use Rvalue::*;
            match rvalue {
                Use(_)
                | Repeat(_, _)
                | ThreadLocalRef(_)
                | Cast(_, _, _)
                | BinaryOp(_, _)
                | NullaryOp(_, _)
                | UnaryOp(_, _)
                | Aggregate(_, _)
                | ShallowInitBox(_, _) => {}

                &Ref(_, _, place)
                | &RawPtr(_, place)
                | &Len(place)
                | &Discriminant(place)
                | &CopyForDeref(place) => {
                    let expansion_reason = match rvalue {
                        Rvalue::Ref(_, kind, _) => ObtainReason::CreateReference(*kind),
                        Rvalue::RawPtr(mutbl, _) => ObtainReason::CreatePtr(*mutbl),
                        _ => ObtainReason::RValueSimpleRead,
                    };
                    if this.stage == StatementStage::Operands && this.preparing {
                        let expansion_actions = this.domain.post_state_mut().obtain(
                            this.repacker,
                            place.into(),
                            location,
                            expansion_reason,
                        );
                        match expansion_actions {
                            Ok(actions) => {
                                this.record_actions(actions);
                            }
                            Err(e) => {
                                this.domain.report_error(e);
                            }
                        }
                    }
                }
            }
        }
        visit_rvalue_inner(self, rvalue, location)
    }
}

struct LifetimeExtractor<'tcx> {
    lifetimes: Vec<ty::Region<'tcx>>,
}

impl<'tcx> TypeVisitor<ty::TyCtxt<'tcx>> for LifetimeExtractor<'tcx> {
    fn visit_region(&mut self, rr: ty::Region<'tcx>) {
        if !self.lifetimes.contains(&rr) {
            self.lifetimes.push(rr);
        }
    }
}

/// Returns all of the (possibly nested) regions in `ty`. If this type is a
/// reference type, e.g. `&'a mut T`, then this will return `'a` and the regions of
/// `T`.
///
/// The resulting list does not contain duplicates, e.g. T<'a, 'a> will return
/// `['a]`. Note that the order of the returned regions is arbitrary, but
/// consistent between calls to shapes with the same "type". E.g T<'a, 'b> and
/// T<'c, 'd> will return the same list of regions will return `['a, 'b]` and
/// `['c, 'd]` respectively. This enables substitution of regions to handle
/// moves in the PCG e.g for the statement `let x: T<'a, 'b> = move c: T<'c,
/// 'd>`.
pub(crate) fn extract_regions(ty: ty::Ty<'_>) -> IndexVec<RegionIdx, PCGRegion> {
    let mut visitor = LifetimeExtractor { lifetimes: vec![] };
    ty.visit_with(&mut visitor);
    IndexVec::from_iter(visitor.lifetimes.iter().map(|r| (*r).into()))
}
