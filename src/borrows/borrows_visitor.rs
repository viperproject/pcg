use std::{collections::BTreeSet, rc::Rc};

use crate::rustc_interface::{
    ast::Mutability,
    borrowck::{
        borrow_set::BorrowSet,
        consumers::{
            BorrowIndex, LocationTable, PoloniusInput, PoloniusOutput, RegionInferenceContext,
        },
    },
    middle::{
        mir::{
            visit::Visitor, AggregateKind, BorrowKind, Const, Location, Operand, Rvalue, Statement,
            StatementKind, Terminator, TerminatorKind,
        },
        ty::{self, Region, RegionKind, RegionVid, TypeVisitable, TypeVisitor},
    },
};

use crate::{
    borrows::{domain::AbstractionBlockEdge, region_abstraction::AbstractionEdge},
    free_pcs::CapabilityKind,
    utils::{self, PlaceRepacker, PlaceSnapshot},
};

use super::{
    borrow_pcg_edge::BlockedNode,
    coupling_graph_constructor::Coupled,
    domain::MaybeOldPlace,
    path_condition::PathConditions,
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

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum StatementStage {
    Operands,
    Main,
}

pub struct BorrowsVisitor<'tcx, 'mir, 'state> {
    repacker: PlaceRepacker<'mir, 'tcx>,
    state: &'state mut BorrowsDomain<'mir, 'tcx>,
    input_facts: &'mir PoloniusInput,
    location_table: &'mir LocationTable,
    borrow_set: Rc<BorrowSet<'tcx>>,
    stage: StatementStage,
    preparing: bool,
    region_inference_context: Rc<RegionInferenceContext<'tcx>>,
    debug_ctx: Option<DebugCtx>,
    #[allow(dead_code)]
    output_facts: &'mir PoloniusOutput,
}

impl<'tcx, 'mir, 'state> BorrowsVisitor<'tcx, 'mir, 'state> {
    pub fn preparing(
        engine: &BorrowsEngine<'mir, 'tcx>,
        state: &'state mut BorrowsDomain<'mir, 'tcx>,
        stage: StatementStage,
    ) -> BorrowsVisitor<'tcx, 'mir, 'state> {
        BorrowsVisitor::new(engine, state, stage, true)
    }

    pub fn applying(
        engine: &BorrowsEngine<'mir, 'tcx>,
        state: &'state mut BorrowsDomain<'mir, 'tcx>,
        stage: StatementStage,
    ) -> BorrowsVisitor<'tcx, 'mir, 'state> {
        BorrowsVisitor::new(engine, state, stage, false)
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
            region_inference_context: engine.region_inference_context.clone(),
            debug_ctx: None,
            output_facts: engine.output_facts,
        }
    }

    /// Ensures that the place is expanded to exactly the given place. If
    /// `capability` is `Some`, the capability of the expanded place is set to
    /// the given value.
    fn ensure_expansion_to_exactly<T: Into<BlockedNode<'tcx>>>(
        &mut self,
        node: T,
        location: Location,
        capability: Option<CapabilityKind>,
    ) {
        self.state.after_state_mut().ensure_expansion_to_exactly(
            self.repacker,
            node.into(),
            location,
            capability,
        );
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
        destination: utils::Place<'tcx>,
        location: Location,
    ) {
        let (func_def_id, substs) = if let Operand::Constant(box c) = func
            && let Const::Val(_, ty) = c.const_
            && let ty::TyKind::FnDef(def_id, substs) = ty.kind()
        {
            (def_id, substs)
        } else {
            unreachable!()
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
        let param_env = self.repacker.tcx().param_env(func_def_id);
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
                            let input_rp = input_place.region_projection(0, self.repacker);
                            let mut ug = UnblockGraph::new();
                            ug.unblock_node(
                                input_rp.into(),
                                &self.state.states.after,
                                self.repacker,
                            );
                            self.state.states.after.apply_unblock_graph(
                                ug,
                                self.repacker,
                                location,
                            );
                            edges.push(AbstractionBlockEdge::new(
                                vec![input_rp.into()].into_iter().collect(),
                                vec![output.into()].into_iter().collect(),
                            ));
                        }
                    }
                    *ty
                }
                _ => *ty,
            };
            for (lifetime_idx, input_lifetime) in extract_regions(ty).into_iter().enumerate() {
                for output in self.matches_for_input_lifetime(
                    input_lifetime,
                    param_env,
                    substs,
                    sig.output(),
                    destination.into(),
                ) {
                    edges.push(AbstractionBlockEdge::new(
                        vec![input_place
                            .region_projection(lifetime_idx, self.repacker)
                            .into()]
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
            self.state.states.after.add_region_abstraction(
                AbstractionEdge::new(AbstractionType::FunctionCall(FunctionCallAbstraction::new(
                    location,
                    *func_def_id,
                    substs,
                    edges.clone(),
                ))),
                location.block,
                self.repacker,
            );
        }
        for edge in edges {
            for output in edge.outputs() {
                if let Some(place) = output.deref(self.repacker) {
                    self.state.states.after.add_region_projection_member(
                        RegionProjectionMember::new(
                            place.into(),
                            Coupled(vec![output]),
                            RegionProjectionMemberDirection::PlaceBlocksProjection,
                        ),
                        PathConditions::AtBlock(location.block),
                        self.repacker,
                    );
                }
            }
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
                    result.push(output_place.region_projection(0, self.repacker));
                }
                *ty
            }
            _ => output_ty,
        };
        for (output_lifetime_idx, output_lifetime) in
            extract_regions(output_ty).into_iter().enumerate()
        {
            if outlives_in_param_env(input_lifetime, output_lifetime, param_env) {
                result.push(output_place.region_projection(output_lifetime_idx, self.repacker));
            }
        }
        result
    }

    fn minimize(&mut self, location: Location) {
        self.state.states.after.minimize(self.repacker, location);
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
        if self.stage == StatementStage::Operands && self.preparing {
            if let Some(place) = operand.place() {
                self.ensure_expansion_to_exactly(place, location, None);
            }
        }
        if self.stage == StatementStage::Main && !self.preparing {
            if let Operand::Move(place) = operand {
                let place: utils::Place<'tcx> = (*place).into();
                self.state
                    .states
                    .after
                    .make_place_old(place, self.repacker, None);
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
                    self.state.states.after.set_latest(
                        (*destination).into(),
                        location,
                        self.repacker,
                    );
                    self.construct_region_abstraction_if_necessary(
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

        for loan in self.loans_invalidated_at(location, self.stage == StatementStage::Operands) {
            let loan = &self.borrow_set[loan];
            self.state
                .states
                .after
                .kill_borrows(loan.reserve_location, location, self.repacker);
        }

        // Will be included as start bridge ops
        if self.preparing && self.stage == StatementStage::Operands {
            match &statement.kind {
                StatementKind::Assign(box (target, _)) => {
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
                        self.state.states.after.make_place_old(
                            target,
                            self.repacker,
                            self.debug_ctx,
                        );
                    }
                }

                StatementKind::FakeRead(box (_, place)) => {
                    let place: utils::Place<'tcx> = (*place).into();
                    if !place.is_owned(self.repacker) {
                        if place.is_ref(self.repacker) {
                            self.ensure_expansion_to_exactly(
                                place.project_deref(self.repacker),
                                location,
                                None,
                            );
                        } else {
                            self.ensure_expansion_to_exactly(place, location, None);
                        }
                    }
                }
                _ => {}
            }
        }

        // Stuff in this block will be included as the middle "bridge" ops that
        // are visible to Prusti
        if self.preparing && self.stage == StatementStage::Main {
            match &statement.kind {
                StatementKind::StorageDead(local) => {
                    let place: utils::Place<'tcx> = (*local).into();
                    self.state
                        .states
                        .after
                        .make_place_old(place, self.repacker, self.debug_ctx);
                    self.state
                        .states
                        .after
                        .trim_old_leaves(self.repacker, location);
                }
                StatementKind::Assign(box (target, _)) => {
                    let target: utils::Place<'tcx> = (*target).into();
                    if !target.is_owned(self.repacker) {
                        self.ensure_expansion_to_exactly(
                            target,
                            location,
                            Some(CapabilityKind::Write),
                        );
                    }
                }
                _ => {}
            }
        }

        if !self.preparing && self.stage == StatementStage::Main {
            match &statement.kind {
                StatementKind::Assign(box (target, rvalue)) => {
                    let target: utils::Place<'tcx> = (*target).into();
                    self.state
                        .states
                        .after
                        .set_latest(target, location, self.repacker);
                    if !target.is_owned(self.repacker) {
                        self.state
                            .states
                            .after
                            .set_capability(target, CapabilityKind::Exclusive);
                    }
                    if let Some(mutbl) = target.ref_mutability(self.repacker) {
                        let capability = if mutbl.is_mut() {
                            CapabilityKind::Exclusive
                        } else {
                            CapabilityKind::Read
                        };
                        self.state
                            .states
                            .after
                            .set_capability(target.project_deref(self.repacker), capability);
                    }
                    match rvalue {
                        Rvalue::Aggregate(box kind, fields) => match kind {
                            AggregateKind::Adt(..) | AggregateKind::Tuple => {
                                let target: utils::Place<'tcx> = (*target).into();
                                for (_idx, field) in fields.iter_enumerated() {
                                    match field.ty(self.repacker.body(), self.repacker.tcx()).kind()
                                    {
                                        ty::TyKind::Ref(region, _, _) => {
                                            for proj in target.region_projections(self.repacker) {
                                                if self.outlives(
                                                    get_vid(region).unwrap(),
                                                    proj.region().as_vid().unwrap(),
                                                ) {
                                                    let operand_place: utils::Place<'tcx> =
                                                        field.place().unwrap().into();
                                                    let operand_place = MaybeOldPlace::new(
                                                        operand_place.project_deref(self.repacker),
                                                        Some(location),
                                                    );
                                                    self.state.states.after.add_region_projection_member(
                                                        RegionProjectionMember::new(
                                                            operand_place.into(),
                                                            Coupled(vec![proj]),
                                                            RegionProjectionMemberDirection::ProjectionBlocksPlace,
                                                        ),
                                                        super::path_condition::PathConditions::AtBlock(location.block),
                                                        self.repacker,
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
                            let from: utils::Place<'tcx> = (*from).into();
                            let target: utils::Place<'tcx> = (*target).into();
                            if let Some(mutbl) = from.ref_mutability(self.repacker)
                                && mutbl.is_mut()
                            {
                                self.state.states.after.change_pcs_elem(
                                    MaybeOldPlace::new(
                                        from.project_deref(self.repacker),
                                        Some(self.state.states.after.get_latest(from)),
                                    ),
                                    target.project_deref(self.repacker).into(),
                                );
                            }
                            let moved_place = MaybeOldPlace::new(
                                from,
                                Some(self.state.states.after.get_latest(from)),
                            );
                            for (idx, p) in moved_place
                                .region_projections(self.repacker)
                                .into_iter()
                                .enumerate()
                            {
                                self.state.states.after.change_pcs_elem(
                                    p,
                                    target.region_projection(idx, self.repacker).into(),
                                );
                            }
                            self.state.states.after.delete_descendants_of(
                                MaybeOldPlace::Current { place: from },
                                location,
                                self.repacker,
                            );
                        }
                        Rvalue::Use(Operand::Copy(from)) => {
                            match from.ty(self.repacker.body(), self.repacker.tcx()).ty.kind() {
                                ty::TyKind::Ref(region, _, _) => {
                                    let from: utils::Place<'tcx> = (*from).into();
                                    let target: utils::Place<'tcx> = (*target).into();
                                    self.state.states.after.add_borrow(
                                        from.project_deref(self.repacker).into(),
                                        target.project_deref(self.repacker),
                                        Mutability::Not,
                                        location,
                                        *region, // TODO: This is the region for the place, not the loan, does that matter?
                                        self.repacker,
                                    );
                                }
                                _ => {}
                            }
                        }
                        Rvalue::Ref(region, kind, blocked_place) => {
                            let blocked_place: utils::Place<'tcx> = (*blocked_place).into();
                            let target: utils::Place<'tcx> = (*target).into();
                            let assigned_place = target.project_deref(self.repacker);
                            assert_eq!(
                                self.repacker.tcx().erase_regions(
                                    (*blocked_place)
                                        .ty(self.repacker.body(), self.repacker.tcx())
                                        .ty
                                ),
                                self.repacker.tcx().erase_regions(
                                    (*assigned_place)
                                        .ty(self.repacker.body(), self.repacker.tcx())
                                        .ty
                                )
                            );
                            self.state.states.after.add_borrow(
                                blocked_place.into(),
                                assigned_place,
                                kind.mutability(),
                                location,
                                *region,
                                self.repacker,
                            );
                        }
                        _ => {}
                    }
                }
                _ => {}
            }
            self.state
                .states
                .after
                .trim_old_leaves(self.repacker, location);
        }
    }

    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
        if matches!(rvalue, Rvalue::Ref(_, BorrowKind::Fake(_), _)) {
            return;
        }
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
                if self.stage == StatementStage::Operands && self.preparing {
                    self.ensure_expansion_to_exactly(place, location, None)
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
