use std::{cell::RefCell, rc::Rc};

use tracing::instrument;

use crate::{
    borrows::domain::RemotePlace,
    combined_pcs::PCGError,
    rustc_interface::{
        ast::Mutability,
        borrowck::{
            borrow_set::BorrowSet,
            consumers::{
                BorrowIndex, LocationTable, PoloniusInput, PoloniusOutput, RegionInferenceContext,
            },
        },
        dataflow::{impls::MaybeLiveLocals, Analysis, ResultsCursor},
        middle::{
            mir::{
                visit::Visitor, AggregateKind, BorrowKind, Const, Location, Operand, Rvalue,
                Statement, StatementKind, Terminator, TerminatorKind,
            },
            ty::{self, TypeVisitable, TypeVisitor},
        },
    },
    utils::Place,
};

use crate::{
    borrows::{domain::AbstractionBlockEdge, region_abstraction::AbstractionEdge},
    free_pcs::CapabilityKind,
    utils::{self, PlaceRepacker, PlaceSnapshot},
};

use super::{
    borrow_pcg_action::BorrowPCGAction,
    borrow_pcg_edge::{BorrowPCGEdge, PCGNode},
    borrows_state::ExecutedActions,
    coupling_graph_constructor::{BorrowCheckerInterface, Coupled},
    domain::{MaybeOldPlace, MaybeRemotePlace},
    has_pcs_elem::HasPcsElems,
    path_condition::PathConditions,
    region_projection::{PCGRegion, RegionProjection},
    region_projection_member::RegionProjectionMember,
    unblock_graph::UnblockGraph,
};
use super::{
    domain::{AbstractionOutputTarget, AbstractionType, FunctionCallAbstraction},
    engine::{BorrowsDomain, BorrowsEngine},
};

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
    pub(super) state: &'state mut BorrowsDomain<'mir, 'tcx>,
    input_facts: &'mir PoloniusInput,
    location_table: &'mir LocationTable,
    borrow_set: Rc<BorrowSet<'tcx>>,
    stage: StatementStage,
    preparing: bool,
    debug_ctx: Option<DebugCtx>,
    #[allow(dead_code)]
    output_facts: &'mir PoloniusOutput,
}

#[derive(Clone)]
pub(crate) struct BorrowCheckerImpl<'mir, 'tcx> {
    cursor: Rc<RefCell<ResultsCursor<'mir, 'tcx, MaybeLiveLocals>>>,
    region_cx: Rc<RegionInferenceContext<'tcx>>,
}

impl<'mir, 'tcx> BorrowCheckerImpl<'mir, 'tcx> {
    pub(crate) fn new(
        repacker: &PlaceRepacker<'mir, 'tcx>,
        region_cx: Rc<RegionInferenceContext<'tcx>>,
    ) -> Self {
        let cursor = MaybeLiveLocals
            .into_engine(repacker.tcx(), repacker.body())
            .iterate_to_fixpoint()
            .into_results_cursor(repacker.body());
        Self {
            cursor: Rc::new(RefCell::new(cursor)),
            region_cx,
        }
    }
}

impl<'mir, 'tcx> BorrowCheckerInterface<'tcx> for BorrowCheckerImpl<'mir, 'tcx> {
    fn outlives(&self, sup: PCGRegion, sub: PCGRegion) -> bool {
        match (sup, sub) {
            (PCGRegion::RegionVid(sup), PCGRegion::RegionVid(sub)) => {
                self.region_cx.eval_outlives(sup, sub)
            }
            (PCGRegion::ReStatic, _) => true,
            _ => false,
        }
    }

    fn is_live(&self, node: PCGNode<'tcx>, location: Location) -> bool {
        let local = match node {
            PCGNode::RegionProjection(rp) => {
                if let Some(local) = rp.local() {
                    local
                } else {
                    todo!()
                }
            }
            PCGNode::Place(MaybeRemotePlace::Local(p)) => p.local(),
            _ => {
                return true;
            }
        };
        let mut cursor = self.cursor.as_ref().borrow_mut();
        cursor.seek_before_primary_effect(location);
        // if !cursor.contains(local) {
        //     eprintln!("{:?} is not live after {:?}", local, location);
        // }
        cursor.contains(local)
    }
}

impl<'tcx, 'mir, 'state> BorrowsVisitor<'tcx, 'mir, 'state> {
    fn remove_edge_and_set_latest(&mut self, edge: &BorrowPCGEdge<'tcx>, location: Location) {
        let actions = self.state.post_state_mut().remove_edge_and_set_latest(
            edge,
            location,
            self.repacker,
            "Remove Edge",
        );
        self.record_actions(actions);
    }

    fn curr_actions(&mut self) -> &mut Vec<BorrowPCGAction<'tcx>> {
        match (self.stage, self.preparing) {
            (StatementStage::Operands, true) => self.state.actions.pre_operands.as_mut(),
            (StatementStage::Operands, false) => self.state.actions.post_operands.as_mut(),
            (StatementStage::Main, true) => self.state.actions.pre_main.as_mut(),
            (StatementStage::Main, false) => self.state.actions.post_main.as_mut(),
        }
    }

    fn reset_actions(&mut self) {
        self.curr_actions().clear();
    }

    fn record_actions(&mut self, actions: ExecutedActions<'tcx>) {
        self.curr_actions().extend(actions.actions());
    }

    fn apply_action(&mut self, action: BorrowPCGAction<'tcx>) {
        self.curr_actions().push(action.clone());
        self.state
            .post_state_mut()
            .apply_action(action, self.repacker);
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
            state,
            input_facts: engine.input_facts,
            stage,
            preparing,
            location_table: engine.location_table,
            borrow_set: engine.borrow_set.clone(),
            debug_ctx: None,
            output_facts: engine.output_facts,
        }
    }

    fn connect_outliving_projections(
        &mut self,
        source_proj: RegionProjection<'tcx, MaybeOldPlace<'tcx>>,
        target: Place<'tcx>,
        location: Location,
    ) {
        for target_proj in target.region_projections(self.repacker) {
            if self.outlives(source_proj.region(), target_proj.region()) {
                self.apply_action(BorrowPCGAction::add_region_projection_member(
                    RegionProjectionMember::new(
                        Coupled::singleton(source_proj.into()),
                        Coupled::singleton(target_proj.into()),
                    ),
                    PathConditions::AtBlock(location.block),
                    "Outliving Projection",
                ));
            }
        }
    }

    fn stmt_post_main(&mut self, statement: &Statement<'tcx>, location: Location) {
        assert!(!self.preparing);
        assert!(self.stage == StatementStage::Main);
        match &statement.kind {
            StatementKind::Assign(box (target, rvalue)) => {
                let target: utils::Place<'tcx> = (*target).into();
                self.apply_action(BorrowPCGAction::set_latest(
                    target,
                    location,
                    "Target of Assignment",
                ));
                let state = self.state.post_state_mut();
                if !target.is_owned(self.repacker) {
                    state.set_capability(target, CapabilityKind::Exclusive);
                }
                match rvalue {
                    Rvalue::Aggregate(
                        box (AggregateKind::Adt(..) | AggregateKind::Tuple),
                        fields,
                    ) => {
                        let target: utils::Place<'tcx> = (*target).into();
                        for field in fields.iter() {
                            let operand_place: utils::Place<'tcx> =
                                if let Some(place) = field.place() {
                                    place.into()
                                } else {
                                    continue;
                                };
                            for source_proj in operand_place.region_projections(self.repacker) {
                                let source_proj = source_proj.map_place(|p| {
                                    MaybeOldPlace::new(
                                        p,
                                        Some(self.state.post_state().get_latest(p)),
                                    )
                                });
                                self.connect_outliving_projections(source_proj, target, location);
                            }
                        }
                    }
                    Rvalue::Use(Operand::Constant(box c)) => match c.ty().kind() {
                        ty::TyKind::Ref(const_region, _, _) => {
                            assert!(target.projection.len() == 0);
                            if let ty::TyKind::Ref(target_region, _, _) =
                                target.ty(self.repacker).ty.kind()
                            {
                                self.apply_action(BorrowPCGAction::add_region_projection_member(
                                    RegionProjectionMember::new(
                                        Coupled::singleton(
                                            RegionProjection::new(
                                                (*const_region).into(),
                                                RemotePlace::new(target.as_local().unwrap()),
                                            )
                                            .into(),
                                        ),
                                        Coupled::singleton(
                                            RegionProjection::new((*target_region).into(), target)
                                                .into(),
                                        ),
                                    ),
                                    PathConditions::AtBlock(location.block),
                                    "Assign constant to local",
                                ));
                            }
                        }
                        _ => {}
                    },
                    Rvalue::Use(Operand::Move(from)) => {
                        let from: utils::Place<'tcx> = (*from).into();
                        let target: utils::Place<'tcx> = (*target).into();
                        if let Some(mutbl) = from.ref_mutability(self.repacker)
                            && mutbl.is_mut()
                        {
                            let old_place = MaybeOldPlace::new(from, Some(state.get_latest(from)));
                            let new_place = target;
                            self.apply_action(BorrowPCGAction::rename_place(
                                old_place,
                                new_place.into(),
                            ));
                        }

                        let actions = self.state.post_state_mut().delete_descendants_of(
                            MaybeOldPlace::Current { place: from },
                            location,
                            self.repacker,
                        );
                        self.record_actions(actions);
                    }
                    Rvalue::Use(Operand::Copy(from)) => {
                        let from_place: utils::Place<'tcx> = (*from).into();
                        for (idx, rp) in from_place
                            .region_projections(self.repacker)
                            .iter()
                            .enumerate()
                        {
                            for mut orig_edge in self
                                .state
                                .states
                                .post_main
                                .edges_blocked_by((*rp).into(), self.repacker)
                            {
                                let edge_region_projections: Vec<
                                    &mut RegionProjection<'tcx, MaybeOldPlace<'tcx>>,
                                > = orig_edge.pcs_elems();
                                for output in edge_region_projections {
                                    if *output == (*rp).into() {
                                        *output =
                                            target.region_projection(idx, self.repacker).into()
                                    }
                                }
                                self.state.states.post_main.insert(orig_edge);
                            }
                        }
                    }
                    Rvalue::Ref(region, kind, blocked_place) => {
                        let blocked_place: utils::Place<'tcx> = (*blocked_place).into();
                        let actions = state.add_borrow(
                            blocked_place.into(),
                            target,
                            kind.mutability(),
                            location,
                            *region,
                            self.repacker,
                        );
                        self.record_actions(actions);
                        for source_proj in blocked_place.region_projections(self.repacker) {
                            self.connect_outliving_projections(
                                source_proj.into(),
                                target,
                                location,
                            );
                        }
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }

    fn outlives(&self, sup: PCGRegion, sub: PCGRegion) -> bool {
        self.state.bc.outlives(sup, sub)
    }

    fn loans_invalidated_at(&self, location: Location, start: bool) -> Vec<BorrowIndex> {
        let location = if start {
            self.location_table.start_index(location)
        } else {
            self.location_table.mid_index(location)
        };
        self.input_facts
            .loan_invalidated_at
            .iter()
            .filter_map(|(loan_point, loan)| {
                if *loan_point == location {
                    Some(*loan)
                } else {
                    None
                }
            })
            .collect()
    }

    /// Constructs a function call abstraction, if necessary.
    fn construct_function_call_abstraction(
        &mut self,
        func: &Operand<'tcx>,
        args: &[&Operand<'tcx>],
        destination: utils::Place<'tcx>,
        location: Location,
    ) {
        let (func_def_id, substs) = if let Operand::Constant(box c) = func
            && let Const::Val(_, ty) = c.const_
            && let ty::TyKind::FnDef(def_id, substs) = ty.kind()
        {
            (def_id, substs)
        } else {
            self.state.report_error(PCGError::Unsupported(format!(
                "Non-constant function calls are not yet supported: {:?}",
                func
            )));
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
        let output_lifetimes = extract_regions(sig.output());
        if output_lifetimes.is_empty() {
            return;
        }
        let mut edges = vec![];

        for arg in args.iter() {
            let input_place: utils::Place<'tcx> = match arg.place() {
                Some(place) => place.into(),
                None => continue,
            };
            let input_place = MaybeOldPlace::OldPlace(PlaceSnapshot::new(
                input_place,
                self.state.post_state().get_latest(input_place),
            ));
            let ty = input_place.ty(self.repacker).ty;
            let ty = match ty.kind() {
                ty::TyKind::Ref(region, ty, _) => {
                    let output_borrow_projections =
                        self.projections_borrowing_from_input_lifetime(*region, destination.into());
                    for output in output_borrow_projections {
                        let input_rp = input_place.region_projection(0, self.repacker);
                        for action in UnblockGraph::actions_to_unblock(
                            input_rp.into(),
                            &self.state.post_state(),
                            self.repacker,
                        ) {
                            self.apply_action(BorrowPCGAction::remove_edge(
                                action.edge,
                                "For Function Call Abstraction",
                            ));
                        }
                        edges.push(AbstractionBlockEdge::new(
                            vec![input_rp.into()].into_iter().collect(),
                            vec![output.into()].into_iter().collect(),
                        ));
                    }
                    *ty
                }
                _ => ty,
            };
            for (lifetime_idx, input_lifetime) in extract_regions(ty).into_iter().enumerate() {
                for output in self
                    .projections_borrowing_from_input_lifetime(input_lifetime, destination.into())
                {
                    if let ty::TyKind::Closure(..) = ty.kind() {
                        self.state.report_error(PCGError::Unsupported(format!(
                            "Closures that contain borrows are not yet supported as function arguments: {:?}",
                            location
                        )));
                        return;
                    }
                    let input_rp = input_place.region_projection(lifetime_idx, self.repacker);

                    // Only add the edge if the input projection already exists, i.e.
                    // is blocking something else. Otherwise, there is no point in tracking
                    // when it becomes accessible.
                    if self.state.post_state().contains(input_rp, self.repacker) {
                        edges.push(AbstractionBlockEdge::new(
                            vec![input_rp.into()].into_iter().collect(),
                            vec![output].into_iter().collect(),
                        ));
                    }
                }
            }
        }

        // No edges may be added e.g. if the inputs do not contain any (possibly
        // nested) mutable references
        if !edges.is_empty() {
            let actions =
                self.state.post_state_mut().insert_abstraction_edge(
                    AbstractionEdge::new(AbstractionType::FunctionCall(
                        FunctionCallAbstraction::new(location, *func_def_id, substs, edges.clone()),
                    )),
                    location.block,
                    self.repacker,
                );
            self.record_actions(actions);
        }
    }

    fn projections_borrowing_from_input_lifetime(
        &self,
        input_lifetime: ty::Region<'tcx>,
        output_place: utils::Place<'tcx>,
    ) -> Vec<AbstractionOutputTarget<'tcx>> {
        let mut result = vec![];
        let output_ty = output_place.ty(self.repacker).ty;
        for (output_lifetime_idx, output_lifetime) in
            extract_regions(output_ty).into_iter().enumerate()
        {
            if self.outlives(input_lifetime.into(), output_lifetime.into()) {
                result.push(
                    output_place
                        .region_projection(output_lifetime_idx, self.repacker)
                        .into(),
                );
            }
        }
        result
    }

    fn minimize(&mut self, location: Location) {
        let actions = self
            .state
            .post_state_mut()
            .minimize(self.repacker, location);
        self.record_actions(actions);
    }
}

impl<'tcx, 'mir, 'state> Visitor<'tcx> for BorrowsVisitor<'tcx, 'mir, 'state> {
    fn visit_operand(&mut self, operand: &Operand<'tcx>, location: Location) {
        self.super_operand(operand, location);
        if self.stage == StatementStage::Operands && self.preparing {
            match operand {
                Operand::Copy(place) | Operand::Move(place) => {
                    let capability = if matches!(operand, Operand::Copy(..)) {
                        CapabilityKind::Read
                    } else {
                        CapabilityKind::Exclusive
                    };
                    let place: utils::Place<'tcx> = (*place).into();
                    let expansion_actions = self.state.post_state_mut().ensure_expansion_to(
                        self.repacker,
                        place,
                        location,
                        capability,
                    );
                    self.record_actions(expansion_actions);
                }
                _ => {}
            }
        } else if self.stage == StatementStage::Operands && !self.preparing {
            match operand {
                Operand::Move(place) => {
                    let place: utils::Place<'tcx> = (*place).into();
                    for rp in place.region_projections(self.repacker) {
                        self.state
                            .post_state_mut()
                            .set_capability(rp, CapabilityKind::Write);
                    }
                    self.state
                        .post_state_mut()
                        .set_capability(place, CapabilityKind::Write);
                }
                _ => {}
            }
        } else if self.stage == StatementStage::Main && !self.preparing {
            if let Operand::Move(place) = operand {
                let place: utils::Place<'tcx> = (*place).into();
                self.apply_action(BorrowPCGAction::make_place_old(place));
            }
        }
    }

    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        if self.preparing && self.stage == StatementStage::Operands {
            self.minimize(location);
        }
        self.super_terminator(terminator, location);
        if self.stage == StatementStage::Main && !self.preparing {
            match &terminator.kind {
                TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    ..
                } => {
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
                _ => {}
            }
        }
    }

    fn visit_statement(&mut self, statement: &Statement<'tcx>, location: Location) {
        self.debug_ctx = Some(DebugCtx::new(location));
        if self.preparing && self.stage == StatementStage::Operands {
            self.minimize(location);
        }
        self.super_statement(statement, location);

        {
            // TODO: Check if this logic is still necessary now that more general
            //       liveness information is used.

            let invalidated_loans =
                self.loans_invalidated_at(location, self.stage == StatementStage::Operands);

            for loan in invalidated_loans {
                let loan = &self.borrow_set[loan];
                let unblock_actions = UnblockGraph::actions_to_unblock(
                    loan.assigned_place.into(),
                    self.state.post_state_mut(),
                    self.repacker,
                );
                for action in unblock_actions {
                    self.remove_edge_and_set_latest(&action.edge, location);
                }
            }
        }

        let state = self.state.post_state_mut();

        // Will be included as start bridge ops
        if self.preparing && self.stage == StatementStage::Operands {
            // Remove places that are non longer live based on borrow checker information
            let actions = self.state.states.post_main.pack_old_and_dead_leaves(
                self.repacker,
                location,
                &self.state.bc,
            );
            self.record_actions(actions);

            let state = self.state.post_state_mut();
            match &statement.kind {
                StatementKind::Assign(box (target, rvalue)) => {
                    if let Rvalue::Cast(_, _, ty) = rvalue {
                        if ty.ref_mutability().is_some() {
                            self.state.report_error(PCGError::Unsupported(format!(
                                "Casts to reference-typed values are not yet supported: {:?}",
                                statement
                            )));
                            return;
                        } else if ty.is_unsafe_ptr() {
                            self.state.report_error(PCGError::Unsupported(format!(
                                "Unsafe pointer casts are not yet supported: {:?}",
                                statement
                            )));
                            return;
                        }
                    }
                    // Any references to target should be made old because it
                    // will be overwritten in the assignment.
                    // In principle the target could be made old in the `Main`
                    // stage as well, maybe that makes more sense?
                    if target
                        .ty(self.repacker.body(), self.repacker.tcx())
                        .ty
                        .is_ref()
                    {
                        let target = (*target).into();
                        state.make_place_old(target, self.repacker, self.debug_ctx);
                    }
                }

                StatementKind::FakeRead(box (_, place)) => {
                    let place: utils::Place<'tcx> = (*place).into();
                    if !place.is_owned(self.repacker) {
                        let actions = state.ensure_expansion_to(
                            self.repacker,
                            place,
                            location,
                            CapabilityKind::Read,
                        );
                        self.record_actions(actions);
                    }
                }
                _ => {}
            }
        } else if self.preparing && self.stage == StatementStage::Main {
            // Stuff in this block will be included as the middle "bridge" ops that
            // are visible to Prusti
            match &statement.kind {
                StatementKind::StorageDead(local) => {
                    let place: utils::Place<'tcx> = (*local).into();
                    state.make_place_old(place, self.repacker, self.debug_ctx);
                    let actions = self.state.states.post_main.pack_old_and_dead_leaves(
                        self.repacker,
                        location,
                        &self.state.bc,
                    );
                    self.record_actions(actions);
                }
                StatementKind::Assign(box (target, _)) => {
                    let target: utils::Place<'tcx> = (*target).into();
                    let expansion_actions = self.state.post_state_mut().ensure_expansion_to(
                        self.repacker,
                        target,
                        location,
                        CapabilityKind::Write,
                    );
                    self.record_actions(expansion_actions);
                }
                _ => {}
            }
        } else if !self.preparing && self.stage == StatementStage::Main {
            self.stmt_post_main(statement, location);
        }
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
                    let place: utils::Place<'tcx> = place.into();
                    let capability = if matches!(
                        rvalue,
                        Rvalue::Ref(_, BorrowKind::Mut { .. }, _)
                            | Rvalue::RawPtr(Mutability::Mut, _)
                    ) {
                        CapabilityKind::Exclusive
                    } else {
                        CapabilityKind::Read
                    };
                    if this.stage == StatementStage::Operands && this.preparing {
                        let actions = this.state.post_state_mut().ensure_expansion_to(
                            this.repacker,
                            place,
                            location,
                            capability,
                        );
                        this.record_actions(actions);
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
pub(crate) fn extract_regions<'tcx>(ty: ty::Ty<'tcx>) -> Vec<ty::Region<'tcx>> {
    let mut visitor = LifetimeExtractor { lifetimes: vec![] };
    ty.visit_with(&mut visitor);
    visitor.lifetimes
}

/// Similar to [`extract_regions`], but if the type is a reference type e.g.
/// `&'a mut T`, then this is equivalent to `extract_regions(T)`.
pub(crate) fn extract_nested_regions<'tcx>(ty: ty::Ty<'tcx>) -> Vec<ty::Region<'tcx>> {
    match ty.kind() {
        ty::TyKind::Ref(_, ty, _) => extract_nested_regions(*ty),
        _ => extract_regions(ty),
    }
}
