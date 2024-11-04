use std::{collections::BTreeSet, rc::Rc};

use rustc_interface::{
    ast::Mutability,
    borrowck::{
        borrow_set::BorrowSet,
        consumers::{
            BorrowIndex, LocationTable, PoloniusInput, PoloniusOutput, RegionInferenceContext,
        },
    },
    middle::{
        mir::{
            visit::Visitor, AggregateKind, Body, Const, Location, Operand, Place, Rvalue,
            Statement, StatementKind, Terminator, TerminatorKind,
        },
        ty::{
            self, EarlyBinder, Region, RegionKind, RegionVid, TyCtxt, TypeVisitable, TypeVisitor,
        },
    },
};

use crate::{
    borrows::{domain::AbstractionBlockEdge, region_abstraction::AbstractionEdge},
    rustc_interface,
    utils::{self, PlaceRepacker, PlaceSnapshot},
};

use super::{
    borrows_state::BorrowsState,
    domain::MaybeOldPlace,
    region_projection_member::{RegionProjectionMember, RegionProjectionMemberDirection},
    unblock_graph::UnblockGraph,
};
use super::{
    domain::{AbstractionOutputTarget, AbstractionType, FunctionCallAbstraction},
    engine::{BorrowsDomain, BorrowsEngine},
};

#[derive(Debug, Clone, Copy)]
pub enum DebugCtx {
    Location(Location),
    Other,
}

impl DebugCtx {
    pub fn new(location: Location) -> DebugCtx {
        DebugCtx::Location(location)
    }

    pub fn location(&self) -> Option<Location> {
        match self {
            DebugCtx::Location(location) => Some(*location),
            DebugCtx::Other => None,
        }
    }
}

pub struct BorrowsVisitor<'tcx, 'mir, 'state> {
    tcx: TyCtxt<'tcx>,
    body: &'mir Body<'tcx>,
    state: &'state mut BorrowsDomain<'mir, 'tcx>,
    input_facts: &'mir PoloniusInput,
    location_table: &'mir LocationTable,
    borrow_set: Rc<BorrowSet<'tcx>>,
    before: bool,
    preparing: bool,
    region_inference_context: Rc<RegionInferenceContext<'tcx>>,
    debug_ctx: Option<DebugCtx>,
    #[allow(dead_code)]
    output_facts: &'mir PoloniusOutput,
}

impl<'tcx, 'mir, 'state> BorrowsVisitor<'tcx, 'mir, 'state> {
    fn repacker(&self) -> PlaceRepacker<'_, 'tcx> {
        PlaceRepacker::new(self.body, self.tcx)
    }
    pub fn preparing(
        engine: &BorrowsEngine<'mir, 'tcx>,
        state: &'state mut BorrowsDomain<'mir, 'tcx>,
        before: bool,
    ) -> BorrowsVisitor<'tcx, 'mir, 'state> {
        BorrowsVisitor::new(engine, state, before, true)
    }

    pub fn applying(
        engine: &BorrowsEngine<'mir, 'tcx>,
        state: &'state mut BorrowsDomain<'mir, 'tcx>,
        before: bool,
    ) -> BorrowsVisitor<'tcx, 'mir, 'state> {
        BorrowsVisitor::new(engine, state, before, false)
    }

    fn new(
        engine: &BorrowsEngine<'mir, 'tcx>,
        state: &'state mut BorrowsDomain<'mir, 'tcx>,
        before: bool,
        preparing: bool,
    ) -> BorrowsVisitor<'tcx, 'mir, 'state> {
        BorrowsVisitor {
            tcx: engine.tcx,
            body: engine.body,
            state,
            input_facts: engine.input_facts,
            before,
            preparing,
            location_table: engine.location_table,
            borrow_set: engine.borrow_set.clone(),
            region_inference_context: engine.region_inference_context.clone(),
            debug_ctx: None,
            output_facts: engine.output_facts,
        }
    }

    fn after_state_mut(&mut self) -> &mut BorrowsState<'tcx> {
        &mut self.state.states.after
    }

    fn ensure_expansion_to_exactly(&mut self, place: utils::Place<'tcx>, location: Location) {
        self.state
            .after_state_mut()
            .ensure_expansion_to_exactly(self.tcx, self.body, place, location)
    }

    fn _loans_invalidated_at(&self, location: Location, start: bool) -> Vec<BorrowIndex> {
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

    fn outlives(&self, sup: RegionVid, sub: RegionVid) -> bool {
        let mut visited = BTreeSet::default();
        let mut stack = vec![sup];

        while let Some(current) = stack.pop() {
            if current == sub {
                return true;
            }

            if visited.insert(current) {
                for o in self
                    .region_inference_context
                    .outlives_constraints()
                    .filter(|c| c.sup == current)
                {
                    stack.push(o.sub);
                }
            }
        }

        false
    }

    fn construct_region_abstraction_if_necessary(
        &mut self,
        func: &Operand<'tcx>,
        args: &[&Operand<'tcx>],
        destination: Place<'tcx>,
        location: Location,
    ) {
        let (func_def_id, substs) = match func {
            Operand::Constant(box c) => match c.const_ {
                Const::Val(_, ty) => match ty.kind() {
                    ty::TyKind::FnDef(def_id, substs) => (def_id, substs),
                    _ => unreachable!(),
                },
                _ => unreachable!(),
            },
            _ => unreachable!(),
        };
        let sig = EarlyBinder::instantiate_identity(self.tcx.fn_sig(func_def_id));
        let sig = self.tcx.liberate_late_bound_regions(*func_def_id, sig);
        let output_lifetimes = extract_lifetimes(sig.output());
        if output_lifetimes.is_empty() {
            return;
        }
        let param_env = self.tcx.param_env(func_def_id);
        let mut edges = vec![];

        for (idx, ty) in sig.inputs().iter().enumerate() {
            let input_place: utils::Place<'tcx> = match args[idx].place() {
                Some(place) => place.into(),
                None => continue,
            };
            let input_place = MaybeOldPlace::OldPlace(PlaceSnapshot::new(
                input_place,
                self.state.states.after.get_latest(input_place),
            ));
            let ty = match ty.kind() {
                ty::TyKind::Ref(region, ty, m) => {
                    if m.is_mut() {
                        for output in self.matches_for_input_lifetime(
                            *region,
                            param_env,
                            substs,
                            sig.output(),
                            destination.into(),
                        ) {
                            edges.push(AbstractionBlockEdge::new(
                                vec![input_place.region_projection(0, self.repacker())]
                                    .into_iter()
                                    .collect(),
                                vec![output].into_iter().collect(),
                            ));
                        }
                    }
                    *ty
                }
                _ => *ty,
            };
            for (lifetime_idx, input_lifetime) in extract_lifetimes(ty).into_iter().enumerate() {
                for output in self.matches_for_input_lifetime(
                    input_lifetime,
                    param_env,
                    substs,
                    sig.output(),
                    destination.into(),
                ) {
                    edges.push(AbstractionBlockEdge::new(
                        vec![input_place.region_projection(lifetime_idx, self.repacker())]
                            .into_iter()
                            .collect(),
                        vec![output].into_iter().collect(),
                    ));
                }
            }
        }

        // No edges may be added e.g. if the inputs do not contain any (possibly
        // nested) mutable references
        if !edges.is_empty() {
            self.after_state_mut().add_region_abstraction(
                AbstractionEdge::new(AbstractionType::FunctionCall(FunctionCallAbstraction::new(
                    location,
                    *func_def_id,
                    substs,
                    edges,
                ))),
                location.block,
            );
        }
    }

    fn matches_for_input_lifetime(
        &self,
        input_lifetime: ty::Region<'tcx>,
        param_env: ty::ParamEnv<'tcx>,
        _substs: ty::GenericArgsRef<'tcx>,
        output_ty: ty::Ty<'tcx>,
        output_place: utils::Place<'tcx>,
    ) -> Vec<AbstractionOutputTarget<'tcx>> {
        let mut result = vec![];
        let output_ty = match output_ty.kind() {
            ty::TyKind::Ref(output_lifetime, ty, Mutability::Mut) => {
                if outlives_in_param_env(input_lifetime, *output_lifetime, param_env) {
                    result.push(output_place.region_projection(0, self.repacker()));
                }
                *ty
            }
            _ => output_ty,
        };
        for (output_lifetime_idx, output_lifetime) in
            extract_lifetimes(output_ty).into_iter().enumerate()
        {
            if outlives_in_param_env(input_lifetime, output_lifetime, param_env) {
                result.push(output_place.region_projection(output_lifetime_idx, self.repacker()));
            }
        }
        result
    }

    fn minimize(&mut self, location: Location) {
        let repacker = PlaceRepacker::new(self.body, self.tcx);
        self.state.states.after.minimize(repacker, location);
    }
}

fn outlives_in_param_env<'tcx>(
    input_lifetime: ty::Region<'tcx>,
    output_lifetime: ty::Region<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
) -> bool {
    if input_lifetime == output_lifetime {
        return true;
    }
    for bound in param_env.caller_bounds() {
        match bound.as_region_outlives_clause() {
            Some(outlives) => {
                let outlives = outlives.no_bound_vars().unwrap();
                if outlives.0 == input_lifetime && outlives.1 == output_lifetime {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}

pub fn get_vid(region: &Region) -> Option<RegionVid> {
    match region.kind() {
        RegionKind::ReVar(vid) => Some(vid),
        _other => None,
    }
}

impl<'tcx, 'mir, 'state> Visitor<'tcx> for BorrowsVisitor<'tcx, 'mir, 'state> {
    fn visit_operand(&mut self, operand: &Operand<'tcx>, location: Location) {
        self.super_operand(operand, location);
        if self.before && self.preparing {
            match operand {
                Operand::Copy(place) | Operand::Move(place) => {
                    let place: utils::Place<'tcx> = (*place).into();
                    self.ensure_expansion_to_exactly(place, location);
                }
                _ => {}
            }
            match operand {
                Operand::Move(place) => {
                    self.state
                        .states
                        .after
                        .set_latest((*place).into(), location);
                    self.state.states.after.make_place_old(
                        (*place).into(),
                        PlaceRepacker::new(self.body, self.tcx),
                        None,
                    );
                }
                _ => {}
            }
        }
    }

    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        if self.preparing && self.before {
            self.minimize(location);
        }
        self.super_terminator(terminator, location);
        if !self.before && !self.preparing {
            match &terminator.kind {
                TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    ..
                } => {
                    self.after_state_mut()
                        .set_latest((*destination).into(), location);
                    self.construct_region_abstraction_if_necessary(
                        func,
                        &args.iter().map(|arg| &arg.node).collect::<Vec<_>>(),
                        (*destination).into(),
                        location,
                    );
                }
                _ => {}
            }
        }
    }

    fn visit_statement(&mut self, statement: &Statement<'tcx>, location: Location) {
        self.debug_ctx = Some(DebugCtx::new(location));
        if self.preparing && self.before {
            self.minimize(location);
        }
        self.super_statement(statement, location);

        // Will be included as start bridge ops
        if self.preparing && self.before {
            match &statement.kind {
                StatementKind::Assign(box (target, _rvalue)) => {
                    if target.ty(self.body, self.tcx).ty.is_ref() {
                        let target = (*target).into();
                        self.state.states.after.make_place_old(
                            target,
                            PlaceRepacker::new(self.body, self.tcx),
                            self.debug_ctx,
                        );
                    }
                }
                StatementKind::FakeRead(box (_, place)) => {
                    let place: utils::Place<'tcx> = (*place).into();
                    if !place.is_owned(self.body, self.tcx) {
                        if place.is_ref(self.body, self.tcx) {
                            self.ensure_expansion_to_exactly(
                                place.project_deref(self.repacker()),
                                location,
                            );
                        } else {
                            self.ensure_expansion_to_exactly(place, location);
                        }
                    }
                }
                _ => {}
            }
        }

        // Stuff in this block will be included as the middle "bridge" ops that
        // are visible to Prusti
        if self.preparing && !self.before {
            match &statement.kind {
                StatementKind::StorageDead(local) => {
                    let place: utils::Place<'tcx> = (*local).into();
                    let repacker = PlaceRepacker::new(self.body, self.tcx);
                    self.state
                        .states
                        .after
                        .make_place_old(place, repacker, self.debug_ctx);
                    self.state.states.after.trim_old_leaves(repacker, location);
                }
                StatementKind::Assign(box (target, _)) => {
                    let target: utils::Place<'tcx> = (*target).into();
                    if !target.is_owned(self.body, self.tcx) {
                        self.ensure_expansion_to_exactly(target, location);
                    }
                }
                _ => {}
            }
        }

        if !self.preparing && !self.before {
            match &statement.kind {
                StatementKind::Assign(box (target, rvalue)) => {
                    self.after_state_mut().set_latest((*target).into(), location);
                    match rvalue {
                        Rvalue::Aggregate(box kind, fields) => match kind {
                            AggregateKind::Adt(..) | AggregateKind::Tuple => {
                                let target: utils::Place<'tcx> = (*target).into();
                                for (_idx, field) in fields.iter_enumerated() {
                                    match field.ty(self.body, self.tcx).kind() {
                                        ty::TyKind::Ref(region, _, _) => {
                                            for proj in target.region_projections(self.repacker()) {
                                                if self.outlives(
                                                    get_vid(region).unwrap(),
                                                    proj.region(),
                                                ) {
                                                    let operand_place: utils::Place<'tcx> =
                                                        field.place().unwrap().into();
                                                    let operand_place = MaybeOldPlace::new(
                                                        operand_place
                                                            .project_deref(self.repacker()),
                                                        Some(location),
                                                    );
                                                    self.state.states.after.add_region_projection_member(
                                                        RegionProjectionMember::new(
                                                            operand_place.into(),
                                                            proj,
                                                            location,
                                                            RegionProjectionMemberDirection::PlaceIsRegionInput,
                                                        ),
                                                    );
                                                }
                                            }
                                        }
                                        _ => {}
                                    }
                                }
                            }
                            _ => {}
                        },
                        Rvalue::Use(Operand::Move(from)) => {
                            let repacker = PlaceRepacker::new(self.body, self.tcx);
                            let from: utils::Place<'tcx> = (*from).into();
                            let target: utils::Place<'tcx> = (*target).into();
                            if matches!(from.ty(self.repacker()).ty.kind(), ty::TyKind::Ref(_, _, r) if r.is_mut())
                            {
                                self.state.states.after.change_pcs_elem(
                                    MaybeOldPlace::new(
                                        from.project_deref(self.repacker()),
                                        Some(self.state.states.after.get_latest(from)),
                                    ),
                                    target.project_deref(repacker).into(),
                                );
                            }
                            let moved_place = MaybeOldPlace::new(
                                from,
                                Some(self.state.states.after.get_latest(from)),
                            );
                            for (idx, p) in moved_place
                                .region_projections(repacker)
                                .into_iter()
                                .enumerate()
                            {
                                self.state.states.after.change_pcs_elem(
                                    p,
                                    target.region_projection(idx, repacker).into(),
                                );
                            }
                            self.state.states.after.delete_descendants_of(
                                MaybeOldPlace::Current { place: from },
                                repacker,
                                location,
                            );
                        }
                        Rvalue::Use(Operand::Copy(from)) => {
                            match from.ty(self.body, self.tcx).ty.kind() {
                                ty::TyKind::Ref(region, _, _) => {
                                    let from: utils::Place<'tcx> = (*from).into();
                                    let target: utils::Place<'tcx> = (*target).into();
                                    self.state.states.after.add_reborrow(
                                        from.project_deref(self.repacker()).into(),
                                        target.project_deref(self.repacker()),
                                        Mutability::Not,
                                        location,
                                        *region, // TODO: This is the region for the place, not the loan, does that matter?
                                    );
                                }
                                _ => {}
                            }
                        }
                        Rvalue::Ref(region, kind, blocked_place) => {
                            let blocked_place: utils::Place<'tcx> = (*blocked_place).into();
                            let target: utils::Place<'tcx> = (*target).into();
                            let assigned_place = target.project_deref(self.repacker());
                            assert_eq!(
                                self.tcx
                                    .erase_regions((*blocked_place).ty(self.body, self.tcx).ty),
                                self.tcx
                                    .erase_regions((*assigned_place).ty(self.body, self.tcx).ty)
                            );
                            self.state.states.after.add_reborrow(
                                blocked_place.into(),
                                assigned_place,
                                kind.mutability(),
                                location,
                                *region,
                            );
                        }
                        _ => {}
                    }
                }
                _ => {}
            }
            let repacker = PlaceRepacker::new(self.body, self.tcx);
            self.state.states.after.trim_old_leaves(repacker, location);
        }
    }

    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
        self.super_rvalue(rvalue, location);
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
                if self.before && self.preparing && !place.is_owned(self.body, self.tcx) {
                    self.ensure_expansion_to_exactly(place, location);
                }
            }
        }
    }
}

struct LifetimeExtractor<'tcx> {
    lifetimes: Vec<ty::Region<'tcx>>,
}

impl<'tcx> TypeVisitor<ty::TyCtxt<'tcx>> for LifetimeExtractor<'tcx> {
    fn visit_region(&mut self, rr: ty::Region<'tcx>) {
        self.lifetimes.push(rr);
    }
}

pub fn extract_lifetimes<'tcx>(ty: ty::Ty<'tcx>) -> Vec<ty::Region<'tcx>> {
    let mut visitor = LifetimeExtractor { lifetimes: vec![] };
    ty.visit_with(&mut visitor);
    visitor.lifetimes
}

pub fn extract_nested_lifetimes<'tcx>(ty: ty::Ty<'tcx>) -> Vec<ty::Region<'tcx>> {
    match ty.kind() {
        ty::TyKind::Ref(_, ty, _) => extract_lifetimes(*ty),
        _ => extract_lifetimes(ty),
    }
}
