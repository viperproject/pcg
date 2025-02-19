use std::{cell::RefCell, rc::Rc};

use crate::{
    combined_pcs::EvalStmtPhase::*, rustc_interface::dataflow::compute_fixpoint,
    validity_checks_enabled,
};
use smallvec::smallvec;
use tracing::instrument;

use crate::{
    borrows::{
        borrow_pcg_edge::BorrowPCGEdgeLike, region_projection::MaybeRemoteRegionProjectionBase,
        region_projection_member::RegionProjectionMemberKind,
    },
    combined_pcs::{PCGError, PCGNode, PCGNodeLike, PCGUnsupportedError},
    rustc_interface::{
        borrowck::{
            BorrowSet, {PoloniusOutput, RegionInferenceContext},
        },
        index::IndexVec,
        middle::{
            mir::{
                self,
                visit::{PlaceContext, Visitor},
                AggregateKind, BorrowKind, Const, Location, Operand, Rvalue, Statement,
                StatementKind, Terminator, TerminatorKind,
            },
            ty::{self, TypeVisitable, TypeVisitor},
        },
        mir_dataflow::{impls::MaybeLiveLocals, ResultsCursor},
    },
    utils::Place,
    visualization::{dot_graph::DotGraph, generate_borrows_dot_graph},
};

use super::{
    borrow_pcg_action::BorrowPCGAction,
    borrows_state::{ExecutedActions, ExpansionReason},
    coupling_graph_constructor::BorrowCheckerInterface,
    has_pcs_elem::HasPcsElems,
    path_condition::PathConditions,
    region_projection::{PCGRegion, RegionIdx, RegionProjection},
    region_projection_member::RegionProjectionMember,
    unblock_graph::UnblockGraph,
};
use super::{domain::AbstractionOutputTarget, engine::BorrowsEngine};
use crate::borrows::domain::BorrowsDomain;
use crate::borrows::edge::abstraction::{
    AbstractionBlockEdge, AbstractionType, FunctionCallAbstraction,
};
use crate::utils::place::maybe_old::MaybeOldPlace;
use crate::utils::place::maybe_remote::MaybeRemotePlace;
use crate::{
    free_pcs::CapabilityKind,
    utils::{self, PlaceRepacker, PlaceSnapshot},
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

#[derive(Clone, Debug)]
pub(crate) struct BorrowPCGActions<'tcx>(Vec<BorrowPCGAction<'tcx>>);

impl<'tcx> Default for BorrowPCGActions<'tcx> {
    fn default() -> Self {
        Self(vec![])
    }
}

impl<'tcx> BorrowPCGActions<'tcx> {
    pub(crate) fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    pub(crate) fn iter(&self) -> impl Iterator<Item = &BorrowPCGAction<'tcx>> {
        self.0.iter()
    }

    pub(crate) fn to_vec(self) -> Vec<BorrowPCGAction<'tcx>> {
        self.0
    }

    pub(crate) fn new() -> Self {
        Self(vec![])
    }

    pub(crate) fn first(&self) -> Option<&BorrowPCGAction<'tcx>> {
        self.0.first()
    }

    pub(crate) fn last(&self) -> Option<&BorrowPCGAction<'tcx>> {
        self.0.last()
    }

    pub(crate) fn clear(&mut self) {
        self.0.clear();
    }

    pub(crate) fn extend(&mut self, actions: BorrowPCGActions<'tcx>) {
        if validity_checks_enabled() {
            match (self.last(), actions.first()) {
            (Some(a), Some(b)) => assert_ne!(
                a, b,
                "The last action ({:#?}) is the same as the first action in the list to extend with.",
                a,
            ),
            _ => (),
        }
        }
        self.0.extend(actions.0);
    }

    pub(crate) fn push(&mut self, action: BorrowPCGAction<'tcx>) {
        if validity_checks_enabled() {
            if let Some(last) = self.last() {
                assert!(last != &action, "Action {:?} to be pushed is the same as the last pushed action, this probably a bug.", action);
            }
        }
        self.0.push(action);
    }
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

#[derive(Clone)]
pub(crate) struct BorrowCheckerImpl<'mir, 'tcx> {
    cursor: Rc<RefCell<ResultsCursor<'mir, 'tcx, MaybeLiveLocals>>>,
    region_cx: &'mir RegionInferenceContext<'tcx>,

    // TODO: Use this to determine when two-phase borrows are activated and
    // update the PCG accordingly
    #[allow(unused)]
    borrows: &'mir BorrowSet<'tcx>,
}

impl<'mir, 'tcx> BorrowCheckerImpl<'mir, 'tcx> {
    pub(crate) fn new(
        repacker: PlaceRepacker<'mir, 'tcx>,
        region_cx: &'mir RegionInferenceContext<'tcx>,
        borrows: &'mir BorrowSet<'tcx>,
    ) -> Self {
        let cursor = compute_fixpoint(MaybeLiveLocals, repacker.tcx(), repacker.body())
            .into_results_cursor(repacker.body());
        Self {
            cursor: Rc::new(RefCell::new(cursor)),
            region_cx,
            borrows,
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

    #[rustversion::before(2024-12-14)]
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
        cursor.contains(local)
    }

    #[rustversion::since(2024-12-14)]
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
        cursor.get().contains(local)
    }

    #[rustversion::since(2024-12-14)]
    fn twophase_borrow_activations(
        &self,
        location: Location,
    ) -> std::collections::BTreeSet<Location> {
        self.borrows.activation_map()[&location]
            .iter()
            .map(|idx| self.borrows[*idx].reserve_location())
            .collect()
    }

    #[rustversion::before(2024-12-14)]
    fn twophase_borrow_activations(
        &self,
        location: Location,
    ) -> std::collections::BTreeSet<Location> {
        self.borrows.activation_map[&location]
            .iter()
            .map(|idx| self.borrows[*idx].reserve_location)
            .collect()
    }
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
        kind: impl Fn(usize) -> RegionProjectionMemberKind,
    ) {
        for (idx, target_proj) in target
            .region_projections(self.repacker)
            .into_iter()
            .enumerate()
        {
            if self.outlives(
                source_proj.region(self.repacker),
                target_proj.region(self.repacker),
            ) {
                self.apply_action(BorrowPCGAction::add_region_projection_member(
                    RegionProjectionMember::new(
                        smallvec![source_proj.into()],
                        smallvec![target_proj.into()],
                        kind(idx),
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
                let state = self.domain.post_state_mut();
                if !target.is_owned(self.repacker) {
                    state.set_capability(target.into(), CapabilityKind::Exclusive, self.repacker);
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
                                let source_proj = source_proj.map_base(|p| {
                                    MaybeOldPlace::new(
                                        p,
                                        Some(self.domain.post_main_state().get_latest(p)),
                                    )
                                });
                                self.connect_outliving_projections(
                                    source_proj,
                                    target,
                                    location,
                                    |_| RegionProjectionMemberKind::Todo,
                                );
                            }
                        }
                    }
                    Rvalue::Use(Operand::Constant(box c)) => match c.ty().kind() {
                        ty::TyKind::Ref(const_region, _, _) => {
                            if let ty::TyKind::Ref(target_region, _, _) =
                                target.ty(self.repacker).ty.kind()
                            {
                                self.apply_action(BorrowPCGAction::add_region_projection_member(
                                    RegionProjectionMember::new(
                                        smallvec![RegionProjection::new(
                                            (*const_region).into(),
                                            MaybeRemoteRegionProjectionBase::Const(c.const_),
                                            self.repacker,
                                        )
                                        .to_pcg_node()],
                                        smallvec![RegionProjection::new(
                                            (*target_region).into(),
                                            target,
                                            self.repacker,
                                        )
                                        .into()],
                                        RegionProjectionMemberKind::ConstRef,
                                    ),
                                    PathConditions::AtBlock(location.block),
                                    "Assign constant",
                                ));
                            }
                        }
                        _ => {}
                    },
                    Rvalue::Use(Operand::Move(from)) => {
                        let from: utils::Place<'tcx> = (*from).into();
                        let target: utils::Place<'tcx> = (*target).into();
                        if from.is_ref(self.repacker) {
                            let old_place = MaybeOldPlace::new(from, Some(state.get_latest(from)));
                            let new_place = target;
                            self.apply_action(BorrowPCGAction::rename_place(
                                old_place,
                                new_place.into(),
                            ));
                        }

                        let actions = self.domain.post_state_mut().delete_descendants_of(
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
                            .iter_enumerated()
                        {
                            let post_main = &self.domain.data.states[PostMain];
                            for mut orig_edge in post_main
                                .edges_blocked_by((*rp).into(), self.repacker)
                                .into_iter()
                                .map(|e| e.to_owned_edge())
                                .collect::<Vec<_>>()
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
                                self.domain.data.states.get_mut(PostMain).insert(orig_edge);
                            }
                        }
                    }
                    Rvalue::Ref(region, kind, blocked_place) => {
                        let blocked_place: utils::Place<'tcx> = (*blocked_place).into();
                        if !target.ty(self.repacker).ty.is_ref() {
                            self.domain.report_error(PCGError::unsupported(
                                PCGUnsupportedError::AssignBorrowToNonReferenceType,
                            ));
                            return;
                        }
                        if matches!(kind, BorrowKind::Fake(_)) {
                            return;
                        }
                        state.add_borrow(
                            blocked_place.into(),
                            target,
                            kind.clone(),
                            location,
                            *region,
                            self.repacker,
                        );
                        for source_proj in
                            blocked_place.region_projections(self.repacker).into_iter()
                        {
                            self.connect_outliving_projections(
                                source_proj.into(),
                                target,
                                location,
                                |_| RegionProjectionMemberKind::BorrowOutlives,
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
                self.domain.post_main_state().get_latest(input_place),
            ));
            let ty = input_place.ty(self.repacker).ty;
            let ty = match ty.kind() {
                ty::TyKind::Ref(region, ty, _) => {
                    let output_borrow_projections = self.projections_borrowing_from_input_lifetime(
                        (*region).into(),
                        destination.into(),
                    );
                    for output in output_borrow_projections {
                        let input_rp = input_place.region_projection(0, self.repacker);
                        let actions = UnblockGraph::actions_to_unblock(
                            input_rp.into(),
                            &self.domain.post_main_state(),
                            self.repacker,
                        )
                        .unwrap_or_else(|e| {
                            if let Ok(dot_graph) = generate_borrows_dot_graph(
                                self.repacker,
                                self.domain.data.states[PostMain].graph(),
                            ) {
                                DotGraph::render_with_imgcat(
                                    &dot_graph,
                                    "Borrows graph for unblock actions",
                                )
                                .unwrap_or_else(|e| {
                                    eprintln!("Error rendering borrows graph: {}", e);
                                });
                            }
                            panic!(
                                "Error getting unblock actions to unblock {:?} for function call at {:?}: {:?}",
                                input_rp, location, e
                            );
                        });
                        for action in actions {
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
                        self.domain.report_error(PCGError::unsupported(
                            PCGUnsupportedError::ClosuresCapturingBorrows,
                        ));
                        return;
                    }
                    let input_rp = input_place.region_projection(lifetime_idx, self.repacker);

                    // Only add the edge if the input projection already exists, i.e.
                    // is blocking something else. Otherwise, there is no point in tracking
                    // when it becomes accessible.
                    if self
                        .domain
                        .post_main_state()
                        .contains(input_rp, self.repacker)
                    {
                        edges.push(AbstractionBlockEdge::new(
                            vec![input_rp.into()].into_iter().collect(),
                            vec![output].into_iter().collect(),
                        ));
                    }
                }
            }
        }

        // No edges may be added e.g. if the inputs do not contain any borrows
        if !edges.is_empty() {
            self.domain.post_state_mut().insert_abstraction_edge(
                AbstractionType::FunctionCall(FunctionCallAbstraction::new(
                    location,
                    *func_def_id,
                    substs,
                    edges.clone(),
                )),
                location.block,
                self.repacker,
            );
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
}

impl<'tcx, 'mir, 'state> Visitor<'tcx> for BorrowsVisitor<'tcx, 'mir, 'state> {
    fn visit_operand(&mut self, operand: &Operand<'tcx>, location: Location) {
        self.super_operand(operand, location);
        if self.domain.has_error() {
            return;
        }
        if self.stage == StatementStage::Operands && self.preparing {
            match operand {
                Operand::Copy(place) | Operand::Move(place) => {
                    let expansion_reason = if matches!(operand, Operand::Copy(..)) {
                        ExpansionReason::CopyOperand
                    } else {
                        ExpansionReason::MoveOperand
                    };
                    let place: utils::Place<'tcx> = (*place).into();
                    let expansion_actions = self.domain.post_state_mut().ensure_expansion_to(
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
            match operand {
                Operand::Move(place) => {
                    let place: utils::Place<'tcx> = (*place).into();
                    for rp in place.region_projections(self.repacker) {
                        self.domain.post_state_mut().set_capability(
                            rp.into(),
                            CapabilityKind::Write,
                            self.repacker,
                        );
                    }
                    if !place.is_owned(self.repacker) {
                        self.domain.post_state_mut().set_capability(
                            place.into(),
                            CapabilityKind::Write,
                            self.repacker,
                        );
                    }
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

    #[tracing::instrument(skip(self, terminator), fields(join_iteration = ?self.domain.debug_join_iteration))]
    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        if self.preparing && self.stage == StatementStage::Operands {
            let post_state = self.domain.data.states.get_mut(PostMain);
            let actions =
                post_state.pack_old_and_dead_leaves(self.repacker, location, &self.domain.bc);
            self.record_actions(actions);
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
            self.record_actions(actions);
        }

        self.super_statement(statement, location);

        // Will be included as start bridge ops
        if self.preparing && self.stage == StatementStage::Operands {
            let state = self.domain.post_state_mut();
            match &statement.kind {
                StatementKind::Assign(box (_, rvalue)) => {
                    if let Rvalue::Cast(_, _, ty) = rvalue {
                        if ty.ref_mutability().is_some() {
                            self.domain.report_error(PCGError::unsupported(
                                PCGUnsupportedError::CastToRef,
                            ));
                            return;
                        } else if ty.is_unsafe_ptr() {
                            self.domain.report_error(PCGError::unsupported(
                                PCGUnsupportedError::UnsafePtrCast,
                            ));
                            return;
                        }
                    }
                }

                StatementKind::FakeRead(box (_, place)) => {
                    let place: utils::Place<'tcx> = (*place).into();
                    if !place.is_owned(self.repacker) {
                        let actions = state.ensure_expansion_to(
                            self.repacker,
                            place,
                            location,
                            ExpansionReason::FakeRead,
                        );
                        match actions {
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
            // Stuff in this block will be included as the middle "bridge" ops that
            // are visible to Prusti
            match &statement.kind {
                StatementKind::StorageDead(local) => {
                    let place: utils::Place<'tcx> = (*local).into();
                    self.apply_action(BorrowPCGAction::make_place_old(place));
                    let actions = self.domain.data.get_mut(PostMain).pack_old_and_dead_leaves(
                        self.repacker,
                        location,
                        &self.domain.bc,
                    );
                    self.record_actions(actions);
                }
                StatementKind::Assign(box (target, _)) => {
                    let target: utils::Place<'tcx> = (*target).into();
                    // Any references to target should be made old because it
                    // will be overwritten in the assignment.
                    if target.is_ref(self.repacker) {
                        self.apply_action(BorrowPCGAction::make_place_old((*target).into()));
                    }
                    let expansion_actions = self.domain.post_state_mut().ensure_expansion_to(
                        self.repacker,
                        target,
                        location,
                        ExpansionReason::AssignTarget,
                    );
                    match expansion_actions {
                        Ok(actions) => {
                            self.record_actions(actions);
                        }
                        Err(e) => {
                            self.domain.report_error(e);
                        }
                    }

                    if !target.is_owned(self.repacker) {
                        let target_cap = self
                            .domain
                            .post_state_mut()
                            .get_capability(target.into())
                            .unwrap();
                        if target_cap != CapabilityKind::Write {
                            self.apply_action(BorrowPCGAction::weaken(
                                target,
                                target_cap,
                                CapabilityKind::Write,
                            ));
                        }
                    }
                }
                _ => {}
            }
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
                        Rvalue::Ref(_, kind, _) => ExpansionReason::CreateReference(*kind),
                        Rvalue::RawPtr(mutbl, _) => ExpansionReason::CreatePtr(*mutbl),
                        _ => ExpansionReason::RValueSimpleRead,
                    };
                    if this.stage == StatementStage::Operands && this.preparing {
                        match this.domain.post_state_mut().ensure_expansion_to(
                            this.repacker,
                            place.into(),
                            location,
                            expansion_reason,
                        ) {
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
pub(crate) fn extract_regions<'tcx>(ty: ty::Ty<'tcx>) -> IndexVec<RegionIdx, PCGRegion> {
    let mut visitor = LifetimeExtractor { lifetimes: vec![] };
    ty.visit_with(&mut visitor);
    IndexVec::from_iter(visitor.lifetimes.iter().map(|r| (*r).into()))
}
