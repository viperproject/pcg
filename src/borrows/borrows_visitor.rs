use std::rc::Rc;

use crate::{
    combined_pcs::PCGError,
    rustc_interface::{
        ast::Mutability,
        borrowck::{
            borrow_set::BorrowSet,
            consumers::{
                BorrowIndex, LocationTable, PoloniusInput, PoloniusOutput, RegionInferenceContext,
            },
        },
        middle::{
            mir::{
                visit::Visitor, AggregateKind, BorrowKind, Const, Location, Operand, Rvalue,
                Statement, StatementKind, Terminator, TerminatorKind,
            },
            ty::{self, Region, RegionKind, RegionVid, TypeVisitable, TypeVisitor},
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
    coupling_graph_constructor::Coupled,
    domain::MaybeOldPlace,
    has_pcs_elem::HasPcsElems,
    path_condition::PathConditions,
    region_projection::RegionProjection,
    region_projection_member::RegionProjectionMember,
    unblock_graph::{UnblockGraph, UnblockType},
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

pub(crate) struct BorrowsVisitor<'tcx, 'mir, 'state> {
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

    /// Ensures that the place is expanded to the given place, possibly for a
    /// certain capability. If `capability` is `Some`, the capability of the
    /// expanded place is set to the given value.
    fn ensure_expansion_to<T: Into<Place<'tcx>>>(
        &mut self,
        node: T,
        location: Location,
        capability: Option<CapabilityKind>,
    ) {
        self.state.after_state_mut().ensure_expansion_to(
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
        self.region_inference_context.eval_outlives(sup, sub)
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
        let mut edges = vec![];

        for arg in args.iter() {
            let input_place: utils::Place<'tcx> = match arg.place() {
                Some(place) => place.into(),
                None => continue,
            };
            let input_place = MaybeOldPlace::OldPlace(PlaceSnapshot::new(
                input_place,
                self.state.states.after.get_latest(input_place),
            ));
            let ty = input_place.ty(self.repacker).ty;
            let ty = match ty.kind() {
                ty::TyKind::Ref(region, ty, _) => {
                    let output_borrow_projections =
                        self.projections_borrowing_from_input_lifetime(*region, destination.into());
                    for output in output_borrow_projections {
                        let input_rp = input_place.region_projection(0, self.repacker);
                        let mut ug = UnblockGraph::new();
                        ug.unblock_node(
                            input_rp.into(),
                            &self.state.states.after,
                            self.repacker,
                            UnblockType::ForExclusive,
                        );
                        self.state
                            .states
                            .after
                            .apply_unblock_graph(ug, self.repacker, location);
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
            self.state.states.after.insert_abstraction_edge(
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
                            Coupled::singleton(output.into()),
                            Coupled::singleton(place.into()),
                        ),
                        PathConditions::AtBlock(location.block),
                        self.repacker,
                    );
                }
            }
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
            if let Some(input_vid) = get_vid(&input_lifetime)
                && let Some(output_vid) = get_vid(&output_lifetime)
                && self.outlives(input_vid, output_vid)
            {
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
        self.state.states.after.minimize(self.repacker, location);
    }
}

pub(crate) fn get_vid(region: &Region) -> Option<RegionVid> {
    match region.kind() {
        RegionKind::ReVar(vid) => Some(vid),
        _other => None,
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
                    self.ensure_expansion_to(place, location, Some(capability));
                }
                _ => {}
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

        for loan in self.loans_invalidated_at(location, self.stage == StatementStage::Operands) {
            let loan = &self.borrow_set[loan];
            let mut ug = UnblockGraph::new();
            ug.unblock_node(
                loan.assigned_place.into(),
                &self.state.states.after,
                self.repacker,
                UnblockType::ForExclusive,
            );
            self.state
                .states
                .after
                .apply_unblock_graph(ug, self.repacker, location);
        }

        // Will be included as start bridge ops
        if self.preparing && self.stage == StatementStage::Operands {
            match &statement.kind {
                StatementKind::Assign(box (target, rvalue)) => {
                    // Any references to target should be made old because it
                    // will be overwritten in the assignment.
                    // In principle the target could be made old in the `Main`
                    // stage as well, maybe that makes more sense?
                    if target
                        .ty(self.repacker.body(), self.repacker.tcx())
                        .ty
                        .is_ref()
                    {
                        if let Rvalue::Cast(_, _, _) = rvalue {
                            self.state.report_error(PCGError::Unsupported(format!(
                                "Casts to reference-typed values are not yet supported: {:?}",
                                statement
                            )));
                            return;
                        }
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
                            self.ensure_expansion_to(
                                place.project_deref(self.repacker),
                                location,
                                None,
                            );
                        } else {
                            self.ensure_expansion_to(place, location, None);
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
                    self.ensure_expansion_to(target, location, Some(CapabilityKind::Write));
                }
                _ => {}
            }
        }

        if !self.preparing && self.stage == StatementStage::Main {
            if let StatementKind::Assign(box (target, rvalue)) = &statement.kind {
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
                                let source_proj = source_proj
                                    .map_place(|p| MaybeOldPlace::new(p, Some(location)));
                                for target_proj in target.region_projections(self.repacker) {
                                    if self.outlives(
                                        source_proj.region().as_vid().unwrap(),
                                        target_proj.region().as_vid().unwrap(),
                                    ) {
                                        self.state.states.after.add_region_projection_member(
                                            RegionProjectionMember::new(
                                                Coupled::singleton(source_proj.into()),
                                                Coupled::singleton(target_proj.into()),
                                            ),
                                            PathConditions::AtBlock(location.block),
                                            self.repacker,
                                        );
                                    }
                                }
                            }
                        }
                    }
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
                        for (idx, old_rp) in moved_place
                            .region_projections(self.repacker)
                            .into_iter()
                            .enumerate()
                        {
                            let new_rp = target.region_projection(idx, self.repacker);
                            // Both of these statements are required! We represent some reigonprojections
                            // as RegionProjection<MaybeOldPlace> and some as RegionProjection<MaybeRemotePlace>,
                            // existing nodes could be of either kind.
                            self.state
                                .states
                                .after
                                .change_pcs_elem::<RegionProjection<'tcx, MaybeOldPlace<'tcx>>>(
                                    old_rp,
                                    new_rp.into(),
                                );
                            self.state
                                .states
                                .after
                                .change_pcs_elem::<RegionProjection<'tcx>>(
                                    old_rp.into(),
                                    new_rp.into(),
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
                        let from_place: utils::Place<'tcx> = (*from).into();
                        for (idx, rp) in from_place
                            .region_projections(self.repacker)
                            .iter()
                            .enumerate()
                        {
                            for mut orig_edge in self
                                .state
                                .states
                                .after
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
                                self.state.states.after.insert(orig_edge);
                            }
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
                    self.ensure_expansion_to(place, location, None)
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
