use itertools::Itertools;
use tracing::instrument;

use crate::action::PcgAction;
use crate::borrow_pcg::action::executed_actions::ExecutedActions;
use crate::borrow_pcg::action::{BorrowPCGAction, MakePlaceOldReason};
use crate::borrow_pcg::borrow_pcg_edge::{BorrowPCGEdge, BorrowPCGEdgeLike, LocalNode};
use crate::borrow_pcg::edge::abstraction::{
    AbstractionBlockEdge, AbstractionType, FunctionCallAbstraction,
};
use crate::borrow_pcg::edge::kind::BorrowPCGEdgeKind;
use crate::borrow_pcg::edge::outlives::{BorrowFlowEdge, BorrowFlowEdgeKind};
use crate::borrow_pcg::edge_data::EdgeData;
use crate::borrow_pcg::graph::frozen::FrozenGraphRef;
use crate::borrow_pcg::path_condition::PathConditions;
use crate::borrow_pcg::region_projection::{
    MaybeRemoteRegionProjectionBase, PcgRegion, RegionProjection, RegionProjectionBaseLike,
    RegionProjectionLabel,
};
use crate::borrow_pcg::state::obtain::ObtainReason;
use crate::free_pcs::triple::TripleWalker;
use crate::free_pcs::{CapabilityKind, RepackOp};
use crate::pcg::{MaybeHasLocation, PCGNode};
use crate::pcg_validity_assert;
use crate::rustc_interface::middle::mir::{
    self, Location, Operand, Rvalue, Statement, StatementKind, Terminator,
};

use crate::action::PcgActions;
use crate::rustc_interface::data_structures::fx::FxHashSet;
use crate::rustc_interface::middle::ty::{self};
use crate::utils::display::DisplayWithCompilerCtxt;
use crate::utils::maybe_old::MaybeOldPlace;
use crate::utils::maybe_remote::MaybeRemotePlace;
use crate::utils::visitor::FallableVisitor;
use crate::utils::{self, CompilerCtxt, HasPlace, Place, PlaceSnapshot, SnapshotLocation};

use super::{AnalysisObject, EvalStmtPhase, PCGUnsupportedError, Pcg, PcgError};

pub(crate) struct CombinedVisitor<'pcg, 'mir, 'tcx> {
    pcg: &'pcg mut Pcg<'tcx>,
    ctxt: CompilerCtxt<'mir, 'tcx>,
    actions: PcgActions<'tcx>,
    phase: EvalStmtPhase,
    tw: &'pcg TripleWalker<'mir, 'tcx>,
}

impl<'pcg, 'mir, 'tcx> CombinedVisitor<'pcg, 'mir, 'tcx> {
    fn outlives(&self, sup: PcgRegion, sub: PcgRegion) -> bool {
        self.ctxt.bc.outlives(sup, sub)
    }

    pub(super) fn make_function_call_abstraction(
        &mut self,
        func: &Operand<'tcx>,
        args: &[&Operand<'tcx>],
        destination: utils::Place<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        // This is just a performance optimization
        if self
            .pcg
            .borrow
            .graph()
            .has_function_call_abstraction_at(location)
        {
            return Ok(());
        }
        let func_ty = func.ty(self.ctxt.body(), self.ctxt.tcx());
        let (func_def_id, substs) = if let ty::TyKind::FnDef(def_id, substs) = func_ty.kind() {
            (def_id, substs)
        } else {
            panic!("Expected a function definition");
        };

        let mk_create_edge_action = |input, output| {
            let edge = BorrowPCGEdge::new(
                AbstractionType::FunctionCall(FunctionCallAbstraction::new(
                    location,
                    *func_def_id,
                    substs,
                    AbstractionBlockEdge::new(input, output),
                ))
                .into(),
                PathConditions::AtBlock(location.block),
            );
            BorrowPCGAction::add_edge(edge, true)
        };

        // The versions of the region projections for the function inputs just
        // before they were moved out, labelled with their last modification
        // time
        let arg_region_projections = args
            .iter()
            .filter_map(|arg| arg.place())
            .flat_map(|mir_place| {
                let input_place: utils::Place<'tcx> = mir_place.into();
                let input_place = MaybeOldPlace::OldPlace(PlaceSnapshot::new(
                    input_place,
                    self.pcg.borrow.get_latest(input_place),
                ));
                input_place.region_projections(self.ctxt)
            })
            .collect::<Vec<_>>();

        let mut labelled_rps = FxHashSet::default();
        for arg in arg_region_projections.iter() {
            if arg.is_nested_in_local_ty(self.ctxt) {
                self.pcg.borrow.label_region_projection(
                    arg,
                    Some(SnapshotLocation::before(location).into()),
                    self.ctxt,
                );
                labelled_rps
                    .insert(arg.label_projection(SnapshotLocation::before(location).into()));
            }
        }

        let placeholder_targets = labelled_rps
            .iter()
            .flat_map(|rp| {
                self.pcg
                    .borrow
                    .graph()
                    .identify_placeholder_target(*rp, self.ctxt)
            })
            .collect::<FxHashSet<_>>();

        let source_arg_projections = arg_region_projections
            .iter()
            .map(|rp| {
                if rp.is_nested_in_local_ty(self.ctxt) {
                    (*rp).label_projection(SnapshotLocation::before(location).into())
                } else {
                    *rp
                }
            })
            .collect::<Vec<_>>();

        let disjoint_lifetime_sets = get_disjoint_lifetime_sets(&arg_region_projections, self.ctxt);
        for ls in disjoint_lifetime_sets.iter() {
            let this_region = ls.iter().next().unwrap();
            let inputs = source_arg_projections
                .iter()
                .filter(|rp| self.ctxt.bc.outlives(rp.region(self.ctxt), *this_region))
                .map(|rp| (*rp).into())
                .collect::<Vec<_>>();
            let mut outputs = placeholder_targets
                .iter()
                .copied()
                .filter(|rp| self.ctxt.bc.same_region(*this_region, rp.region(self.ctxt)))
                .map(|mut rp| {
                    rp.label = Some(RegionProjectionLabel::Placeholder);
                    rp
                })
                .collect::<Vec<_>>();
            let result_projections: Vec<RegionProjection<MaybeOldPlace<'tcx>>> = destination
                .region_projections(self.ctxt)
                .iter()
                .filter(|rp| self.ctxt.bc.outlives(*this_region, rp.region(self.ctxt)))
                .map(|rp| (*rp).into())
                .collect();
            outputs.extend(result_projections);
            if !inputs.is_empty() && !outputs.is_empty() {
                self.record_and_apply_action(mk_create_edge_action(inputs, outputs).into())?;
            }
        }
        Ok(())
    }

    fn connect_outliving_projections(
        &mut self,
        source_proj: RegionProjection<'tcx, MaybeOldPlace<'tcx>>,
        target: Place<'tcx>,
        location: Location,
        kind: impl Fn(PcgRegion) -> BorrowFlowEdgeKind,
    ) -> Result<(), PcgError> {
        for target_proj in target.region_projections(self.ctxt).into_iter() {
            if self.outlives(source_proj.region(self.ctxt), target_proj.region(self.ctxt)) {
                self.record_and_apply_action(
                    BorrowPCGAction::add_edge(
                        BorrowPCGEdge::new(
                            BorrowFlowEdge::new(
                                source_proj.into(),
                                target_proj.into(),
                                kind(target_proj.region(self.ctxt)),
                                self.ctxt,
                            )
                            .into(),
                            PathConditions::AtBlock(location.block),
                        ),
                        true,
                    )
                    .into(),
                )?;
            }
        }
        Ok(())
    }
    pub(crate) fn stmt_post_main(
        &mut self,
        statement: &Statement<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        assert!(self.phase == EvalStmtPhase::PostMain);
        if let StatementKind::Assign(box (target, rvalue)) = &statement.kind {
            self.assign_post_main((*target).into(), rvalue, location)?;
        }
        Ok(())
    }

    #[tracing::instrument(skip(self))]
    fn assign_post_main(
        &mut self,
        target: utils::Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        self.record_and_apply_action(
            BorrowPCGAction::set_latest(target, location, "Target of Assignment").into(),
        )?;
        self.pcg
            .capabilities
            .insert(target.into(), CapabilityKind::Exclusive);
        match rvalue {
            Rvalue::Aggregate(
                box (mir::AggregateKind::Adt(..)
                | mir::AggregateKind::Tuple
                | mir::AggregateKind::Array(..)),
                fields,
            ) => {
                let target: utils::Place<'tcx> = (*target).into();
                for (field_idx, field) in fields.iter().enumerate() {
                    let operand_place: utils::Place<'tcx> = if let Some(place) = field.place() {
                        place.into()
                    } else {
                        continue;
                    };
                    for (source_rp_idx, source_proj) in operand_place
                        .region_projections(self.ctxt)
                        .iter()
                        .enumerate()
                    {
                        let source_proj = source_proj.with_base(
                            MaybeOldPlace::new(
                                source_proj.base,
                                Some(self.pcg.borrow.get_latest(source_proj.base)),
                            ),
                            self.ctxt,
                        );
                        self.connect_outliving_projections(source_proj, target, location, |_| {
                            BorrowFlowEdgeKind::Aggregate {
                                field_idx,
                                target_rp_index: source_rp_idx,
                            }
                        })?;
                    }
                }
            }
            Rvalue::Use(Operand::Constant(box c)) => {
                if let ty::TyKind::Ref(const_region, _, _) = c.ty().kind() {
                    if let ty::TyKind::Ref(target_region, _, _) = target.ty(self.ctxt).ty.kind() {
                        self.record_and_apply_action(
                            BorrowPCGAction::add_edge(
                                BorrowPCGEdge::new(
                                    BorrowFlowEdge::new(
                                        RegionProjection::new(
                                            (*const_region).into(),
                                            MaybeRemoteRegionProjectionBase::Const(c.const_),
                                            None,
                                            self.ctxt,
                                        )
                                        .unwrap(),
                                        RegionProjection::new(
                                            (*target_region).into(),
                                            target,
                                            None,
                                            self.ctxt,
                                        )
                                        .unwrap()
                                        .into(),
                                        BorrowFlowEdgeKind::ConstRef,
                                        self.ctxt,
                                    )
                                    .into(),
                                    PathConditions::AtBlock(location.block),
                                ),
                                true,
                            )
                            .into(),
                        )?;
                    }
                }
            }
            Rvalue::Use(operand @ (Operand::Move(from) | Operand::Copy(from))) => {
                let from: utils::Place<'tcx> = (*from).into();
                let (from, kind) = if matches!(operand, Operand::Move(_)) {
                    (
                        MaybeOldPlace::new(from, Some(self.pcg.borrow.get_latest(from))),
                        BorrowFlowEdgeKind::Move,
                    )
                } else {
                    (from.into(), BorrowFlowEdgeKind::CopySharedRef)
                };
                for (source_proj, target_proj) in from
                    .region_projections(self.ctxt)
                    .into_iter()
                    .zip(target.region_projections(self.ctxt).into_iter())
                {
                    self.record_and_apply_action(
                        BorrowPCGAction::add_edge(
                            BorrowPCGEdge::new(
                                BorrowFlowEdge::new(
                                    source_proj.into(),
                                    target_proj.into(),
                                    kind,
                                    self.ctxt,
                                )
                                .into(),
                                PathConditions::AtBlock(location.block),
                            ),
                            true,
                        )
                        .into(),
                    )?;
                }
            }
            Rvalue::Ref(borrow_region, kind, blocked_place) => {
                let blocked_place: utils::Place<'tcx> = (*blocked_place).into();
                let blocked_place = blocked_place.with_inherent_region(self.ctxt);
                if !target.ty(self.ctxt).ty.is_ref() {
                    return Err(PcgError::unsupported(
                        PCGUnsupportedError::AssignBorrowToNonReferenceType,
                    ));
                }
                if matches!(kind, mir::BorrowKind::Fake(_)) {
                    return Ok(());
                }
                self.pcg.borrow.add_borrow(
                    blocked_place.into(),
                    target,
                    *kind,
                    location,
                    *borrow_region,
                    &mut self.pcg.capabilities,
                    self.ctxt,
                );
                for mut source_proj in blocked_place.region_projections(self.ctxt).into_iter() {
                    let source_proj = if kind.mutability().is_mut() {
                        self.pcg.borrow.label_region_projection(
                            &source_proj.into(),
                            Some(location.into()),
                            self.ctxt,
                        );
                        source_proj.label = Some(location.into());
                        source_proj
                    } else {
                        source_proj
                    };
                    let source_region = source_proj.region(self.ctxt);
                    for target_proj in target.region_projections(self.ctxt).into_iter() {
                        let target_region = target_proj.region(self.ctxt);
                        if self.ctxt.bc.outlives(source_region, target_region) {
                            let regions_equal =
                                self.ctxt.bc.same_region(source_region, target_region);
                            self.record_and_apply_action(
                                BorrowPCGAction::add_edge(
                                    BorrowPCGEdge::new(
                                        BorrowFlowEdge::new(
                                            source_proj.into(),
                                            target_proj.into(),
                                            BorrowFlowEdgeKind::BorrowOutlives { regions_equal },
                                            self.ctxt,
                                        )
                                        .into(),
                                        PathConditions::AtBlock(location.block),
                                    ),
                                    true,
                                )
                                .into(),
                            )?;
                        }
                    }
                }
            }
            _ => {}
        }
        Ok(())
    }

    #[tracing::instrument(skip(pcg, ctxt, tw, analysis_object, location))]
    pub(crate) fn visit(
        pcg: &'pcg mut Pcg<'tcx>,
        ctxt: CompilerCtxt<'mir, 'tcx>,
        tw: &'pcg TripleWalker<'mir, 'tcx>,
        phase: EvalStmtPhase,
        analysis_object: AnalysisObject<'_, 'tcx>,
        location: Location,
    ) -> Result<PcgActions<'tcx>, PcgError> {
        let visitor = Self::new(pcg, ctxt, tw, phase);
        let actions = visitor.apply(analysis_object, location)?;
        Ok(actions)
    }

    fn collapse_owned_places(&mut self) {
        let mut actions = PcgActions::default();
        for caps in self
            .pcg
            .owned
            .data
            .as_mut()
            .unwrap()
            .capability_projections_mut()
        {
            let mut expansions = caps
                .expansions()
                .clone()
                .into_iter()
                .sorted_by_key(|(p, _)| p.projection.len())
                .collect::<Vec<_>>();
            while let Some((base, expansion)) = expansions.pop() {
                let expansion_places = base.expansion_places(&expansion, self.ctxt);
                if expansion_places
                    .iter()
                    .all(|p| !self.pcg.borrow.graph().contains(*p, self.ctxt))
                    && let Some(candidate_cap) =
                        self.pcg.capabilities.get(expansion_places[0].into())
                    && expansion_places
                        .iter()
                        .all(|p| self.pcg.capabilities.get((*p).into()) == Some(candidate_cap))
                {
                    actions.extend(
                        caps.collapse(base, &mut self.pcg.capabilities, self.ctxt)
                            .unwrap()
                            .into(),
                    );
                }
            }
        }
        self.record_actions(actions.into());
    }

    pub(crate) fn new(
        pcg: &'pcg mut Pcg<'tcx>,
        ctxt: CompilerCtxt<'mir, 'tcx>,
        tw: &'pcg TripleWalker<'mir, 'tcx>,
        phase: EvalStmtPhase,
    ) -> Self {
        Self {
            pcg,
            ctxt,
            actions: PcgActions::default(),
            phase,
            tw,
        }
    }
}

impl<'tcx> FallableVisitor<'tcx> for CombinedVisitor<'_, '_, 'tcx> {
    fn visit_statement_fallable(
        &mut self,
        statement: &Statement<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        self.super_statement_fallable(statement, location)?;
        match self.phase {
            EvalStmtPhase::PreOperands => {
                if let StatementKind::FakeRead(box (_, place)) = &statement.kind {
                    let place: utils::Place<'tcx> = (*place).into();
                    if !place.is_owned(self.ctxt) {
                        let expansion_reason = ObtainReason::FakeRead;
                        let expansion_actions = self.pcg.borrow.obtain(
                            self.ctxt,
                            place,
                            &mut self.pcg.capabilities,
                            &self.pcg.owned,
                            location,
                            expansion_reason,
                        )?;
                        self.record_actions(expansion_actions);
                    }
                }
            }
            EvalStmtPhase::PreMain => {
                match &statement.kind {
                    StatementKind::StorageDead(local) => {
                        let place: utils::Place<'tcx> = (*local).into();
                        self.record_and_apply_action(
                            BorrowPCGAction::make_place_old(place, MakePlaceOldReason::StorageDead)
                                .into(),
                        )?;
                    }
                    StatementKind::Assign(box (target, _)) => {
                        let target: utils::Place<'tcx> = (*target).into();
                        // Any references to target should be made old because it
                        // will be overwritten in the assignment.
                        if target.is_ref(self.ctxt)
                            && self.pcg.borrow.graph().contains(target, self.ctxt)
                        {
                            self.record_and_apply_action(
                                BorrowPCGAction::make_place_old(
                                    (*target).into(),
                                    MakePlaceOldReason::ReAssign,
                                )
                                .into(),
                            )?;

                            // The permission to the target may have been Read originally.
                            // Now, because it's been made old, the non-old place should be a leaf,
                            // and its permission should be Exclusive.
                            if self.pcg.capabilities.get(target.into())
                                == Some(CapabilityKind::Read)
                            {
                                self.record_and_apply_action(
                                    BorrowPCGAction::restore_capability(
                                        target.into(),
                                        CapabilityKind::Exclusive,
                                    )
                                    .into(),
                                )?;
                            }
                        }
                        let obtain_reason = ObtainReason::AssignTarget;
                        let obtain_actions = self.pcg.borrow.obtain(
                            self.ctxt,
                            target,
                            &mut self.pcg.capabilities,
                            &self.pcg.owned,
                            location,
                            obtain_reason,
                        )?;
                        self.actions.extend(obtain_actions.actions());

                        if !target.is_owned(self.ctxt) {
                            if let Some(target_cap) = self.pcg.capabilities.get(target.into()) {
                                if target_cap != CapabilityKind::Write {
                                    pcg_validity_assert!(
                                        target_cap >= CapabilityKind::Write,
                                        "{:?}: {} cap {:?} is not greater than {:?}",
                                        location,
                                        target.to_short_string(self.ctxt),
                                        target_cap,
                                        CapabilityKind::Write
                                    );
                                    self.record_and_apply_action(
                                        BorrowPCGAction::weaken(
                                            target,
                                            target_cap,
                                            Some(CapabilityKind::Write),
                                        )
                                        .into(),
                                    )?;
                                }
                            } else {
                                pcg_validity_assert!(
                                    false,
                                    "No capability found for {}",
                                    target.to_short_string(self.ctxt)
                                );
                            }
                        }
                        for rp in target.region_projections(self.ctxt).into_iter() {
                            let blocked_edges = self
                                .pcg
                                .borrow
                                .graph()
                                .edges_blocked_by(rp.into(), self.ctxt)
                                .map(|edge| edge.to_owned_edge())
                                .collect::<Vec<_>>();
                            for edge in blocked_edges {
                                let should_remove = !matches!(
                                    edge.kind(),
                                    BorrowPCGEdgeKind::BorrowPCGExpansion(_)
                                );
                                if should_remove {
                                    self.remove_edge_and_set_latest(edge, location, "Assign")?;
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
            EvalStmtPhase::PostMain => {
                self.stmt_post_main(statement, location)?;
            }
            _ => {}
        }
        Ok(())
    }

    fn visit_operand_fallable(
        &mut self,
        operand: &Operand<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        self.super_operand_fallable(operand, location)?;
        match self.phase {
            EvalStmtPhase::PreOperands => match operand {
                Operand::Copy(place) | Operand::Move(place) => {
                    let expansion_reason = if matches!(operand, Operand::Copy(..)) {
                        ObtainReason::CopyOperand
                    } else {
                        ObtainReason::MoveOperand
                    };
                    let place: utils::Place<'tcx> = (*place).into();
                    let expansion_actions = self.pcg.borrow.obtain(
                        self.ctxt,
                        place,
                        &mut self.pcg.capabilities,
                        &self.pcg.owned,
                        location,
                        expansion_reason,
                    )?;
                    self.record_actions(expansion_actions);
                }
                _ => {}
            },
            EvalStmtPhase::PostMain => {
                if let Operand::Move(place) = operand {
                    let place: utils::Place<'tcx> = (*place).into();
                    self.record_and_apply_action(
                        BorrowPCGAction::make_place_old(place, MakePlaceOldReason::MoveOut).into(),
                    )?;
                }
            }
            _ => {}
        }
        Ok(())
    }

    fn visit_terminator_fallable(
        &mut self,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        self.super_terminator_fallable(terminator, location)?;
        if self.phase == EvalStmtPhase::PostMain
            && let mir::TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } = &terminator.kind
        {
            let destination: utils::Place<'tcx> = (*destination).into();
            self.record_and_apply_action(
                BorrowPCGAction::set_latest(destination, location, "Destination of Function Call")
                    .into(),
            )?;
            self.make_function_call_abstraction(
                func,
                &args.iter().map(|arg| &arg.node).collect::<Vec<_>>(),
                destination,
                location,
            )?;
        }
        Ok(())
    }

    fn visit_place_fallable(
        &mut self,
        place: utils::Place<'tcx>,
        _context: mir::visit::PlaceContext,
        _location: Location,
    ) -> Result<(), PcgError> {
        if place.contains_unsafe_deref(self.ctxt) {
            return Err(PcgError::unsupported(PCGUnsupportedError::DerefUnsafePtr));
        }
        Ok(())
    }

    fn visit_rvalue_fallable(
        &mut self,
        rvalue: &Rvalue<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        #[instrument(skip(this), fields(location = ?location))]
        fn visit_rvalue_inner<'mir, 'tcx, 'state>(
            this: &mut CombinedVisitor<'_, 'mir, 'tcx>,
            rvalue: &Rvalue<'tcx>,
            location: Location,
        ) -> Result<(), PcgError> {
            if matches!(rvalue, Rvalue::Ref(_, mir::BorrowKind::Fake(_), _)) {
                return Ok(());
            }
            this.super_rvalue_fallable(rvalue, location)?;
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
                    if this.phase == EvalStmtPhase::PreOperands {
                        let expansion_actions = this.pcg.borrow.obtain(
                            this.ctxt,
                            place.into(),
                            &mut this.pcg.capabilities,
                            &this.pcg.owned,
                            location,
                            expansion_reason,
                        )?;
                        this.record_actions(expansion_actions);
                    }
                }
            }
            Ok(())
        }
        visit_rvalue_inner(self, rvalue, location)
    }
}
impl<'tcx> CombinedVisitor<'_, '_, 'tcx> {
    pub(crate) fn apply(
        mut self,
        object: AnalysisObject<'_, 'tcx>,
        location: Location,
    ) -> Result<PcgActions<'tcx>, PcgError> {
        match self.phase {
            EvalStmtPhase::PreOperands => {
                self.perform_borrow_initial_pre_operand_actions(location)?;
                self.collapse_owned_places();
                for triple in self.tw.operand_triples.iter() {
                    self.actions
                        .extend(self.pcg.requires(triple.pre(), self.ctxt)?);
                }
            }
            EvalStmtPhase::PostOperands => {
                for triple in self.tw.operand_triples.iter() {
                    self.pcg.owned_ensures(*triple);
                }
            }
            EvalStmtPhase::PostMain => {
                for triple in self.tw.main_triples.iter() {
                    self.pcg.owned_ensures(*triple)
                }
            }
            _ => {}
        }
        match object {
            AnalysisObject::Statement(statement) => {
                self.visit_statement_fallable(statement, location)?
            }
            AnalysisObject::Terminator(terminator) => {
                self.visit_terminator_fallable(terminator, location)?
            }
        }
        if self.phase == EvalStmtPhase::PreMain {
            for triple in self.tw.main_triples.iter() {
                self.actions
                    .extend(self.pcg.requires(triple.pre(), self.ctxt)?);
            }
        }
        Ok(self.actions)
    }
    #[tracing::instrument(skip(self, edge, location))]
    pub(crate) fn remove_edge_and_set_latest(
        &mut self,
        edge: impl BorrowPCGEdgeLike<'tcx>,
        location: Location,
        context: &str,
    ) -> Result<(), PcgError> {
        for place in edge.blocked_places(self.ctxt) {
            if let Some(place) = place.as_current_place()
                && self.pcg.capabilities.get(place.into()) != Some(CapabilityKind::Read)
                && place.has_location_dependent_value(self.ctxt)
            {
                self.record_and_apply_action(
                    BorrowPCGAction::set_latest(place, location, context).into(),
                )?;
            }
        }
        let remove_edge_action =
            BorrowPCGAction::remove_edge(edge.clone().to_owned_edge(), context);
        self.record_and_apply_action(remove_edge_action.into())?;

        let fg = self.pcg.borrow.graph().frozen_graph();
        let blocked_nodes = edge.blocked_nodes(self.ctxt);
        let to_restore = blocked_nodes
            .into_iter()
            .filter(|node| !fg.has_edge_blocking(*node, self.ctxt))
            .collect::<Vec<_>>();
        for node in to_restore {
            if let Some(place) = node.as_maybe_old_place() {
                let blocked_cap = self.pcg.capabilities.get(place);

                let restore_cap = if place.place().projects_shared_ref(self.ctxt) {
                    CapabilityKind::Read
                } else {
                    CapabilityKind::Exclusive
                };

                if blocked_cap.is_none_or(|bc| bc < restore_cap) {
                    self.record_and_apply_action(PcgAction::restore_capability(
                        place,
                        restore_cap,
                        self.ctxt,
                    ))?;
                }
            }
        }
        for blocked_place in edge.blocked_places(self.ctxt) {
            if let MaybeRemotePlace::Local(place) = blocked_place {
                for mut region_projection in place.region_projections(self.ctxt) {
                    // Remove Placeholder label from the region projection
                    region_projection.label = Some(RegionProjectionLabel::Placeholder);
                    self.pcg
                        .borrow
                        .label_region_projection(&region_projection, None, self.ctxt);
                }
            }
        }

        if let BorrowPCGEdgeKind::BorrowPCGExpansion(expansion) = edge.kind() {
            for node in expansion.expansion() {
                for to_redirect in self
                    .pcg
                    .borrow
                    .graph()
                    .edges_blocked_by(*node, self.ctxt)
                    .map(|e| e.kind.clone())
                    .collect::<Vec<_>>()
                {
                    // TODO: Due to a bug ignore other expansions to this place for now
                    if !matches!(to_redirect, BorrowPCGEdgeKind::BorrowPCGExpansion(_)) {
                        self.pcg
                            .borrow
                            .graph
                            .redirect_edge(to_redirect, *node, expansion.base)
                    }
                }
            }
        }
        Ok(())
    }

    fn record_actions(&mut self, actions: ExecutedActions<'tcx>) {
        self.actions.extend(actions.actions());
    }

    #[tracing::instrument(skip(self))]
    fn record_and_apply_action(&mut self, action: PcgAction<'tcx>) -> Result<bool, PcgError> {
        let result = match &action {
            PcgAction::Borrow(action) => self.pcg.borrow.apply_action(
                action.clone(),
                &mut self.pcg.capabilities,
                self.ctxt,
            )?,
            PcgAction::Owned(action) => match action {
                RepackOp::StorageDead(local) => todo!(),
                RepackOp::IgnoreStorageDead(local) => todo!(),
                RepackOp::Weaken(place, capability_kind, capability_kind1) => todo!(),
                RepackOp::Expand(place, place1, capability_kind) => todo!(),
                RepackOp::Collapse(place, place1, capability_kind) => todo!(),
                RepackOp::DerefShallowInit(place, place1) => todo!(),
                RepackOp::RegainLoanedCapability(place, capability_kind) => self
                    .pcg
                    .capabilities
                    .insert((*place).into(), *capability_kind),
            },
        };
        self.actions.push(action);
        Ok(result)
    }

    /// Removes leaves that are old or dead (based on the borrow checker). This
    /// function should called prior to evaluating the effect of the statement
    /// at `location`.
    ///
    /// Note that the liveness calculation is performed based on what happened
    /// at the end of the *previous* statement.
    ///
    /// For example when evaluating:
    /// ```text
    /// bb0[1]: let x = &mut y;
    /// bb0[2]: *x = 2;
    /// bb0[3]: ... // x is dead
    /// ```
    /// we do not remove the `*x -> y` edge until `bb0[3]`.
    /// This ensures that the edge appears in the graph at the end of `bb0[2]`
    /// (rather than never at all).
    ///
    /// Additional caveat: we do not remove dead places that are function
    /// arguments. At least for now this interferes with the implementation in
    /// the Prusti purified encoding for accessing the final value of a
    /// reference-typed function argument in its postcondition.
    pub(crate) fn pack_old_and_dead_borrow_leaves<'mir>(
        &mut self,
        location: Location,
    ) -> Result<(), PcgError> {
        let mut num_edges_prev = self.pcg.borrow.graph().num_edges();
        loop {
            fn go<'slf, 'mir: 'slf, 'bc: 'slf, 'tcx>(
                slf: &'slf mut Pcg<'tcx>,
                ctxt: CompilerCtxt<'mir, 'tcx>,
                location: Location,
            ) -> Vec<BorrowPCGEdge<'tcx>> {
                let fg = slf.borrow.graph().frozen_graph();

                let should_kill_node = |p: LocalNode<'tcx>, fg: &FrozenGraphRef<'slf, 'tcx>| {
                    let place = match p {
                        PCGNode::Place(p) => p,
                        PCGNode::RegionProjection(rp) => rp.place(),
                    };
                    if place.is_old() {
                        return true;
                    }

                    if ctxt.is_arg(place.local()) {
                        return false;
                    }

                    if !place.place().projection.is_empty()
                        && !fg.has_edge_blocking(place.into(), ctxt)
                    {
                        return true;
                    }

                    ctxt.bc.is_dead(p.into(), location, true) // Definitely a leaf by this point
                };

                let should_pack_edge = |edge: &BorrowPCGEdgeKind<'tcx>| match edge {
                    BorrowPCGEdgeKind::BorrowPCGExpansion(expansion) => {
                        if expansion.expansion().iter().all(|node| {
                            node.is_old() || ctxt.bc.is_dead(node.place().into(), location, true)
                        }) {
                            true
                        } else {
                            expansion.expansion().iter().all(|node| {
                                expansion.base().place().is_prefix_exact(node.place())
                                    && expansion.base().location() == node.location()
                            })
                        }
                    }
                    _ => edge
                        .blocked_by_nodes(ctxt)
                        .iter()
                        .all(|p| should_kill_node(*p, &fg)),
                };

                let mut edges_to_trim = Vec::new();
                for edge in fg.leaf_edges(ctxt).into_iter().map(|e| e.to_owned_edge()) {
                    if should_pack_edge(edge.kind()) {
                        edges_to_trim.push(edge);
                    }
                }
                edges_to_trim
            }
            let edges_to_trim = go(self.pcg, self.ctxt, location);
            if edges_to_trim.is_empty() {
                break Ok(());
            }
            for edge in edges_to_trim {
                self.remove_edge_and_set_latest(edge, location, "Trim Old Leaves")?
            }
            let new_num_edges = self.pcg.borrow.graph().num_edges();
            assert!(new_num_edges <= num_edges_prev);
            num_edges_prev = new_num_edges;
        }
    }

    fn perform_borrow_initial_pre_operand_actions(
        &mut self,
        location: Location,
    ) -> Result<(), PcgError> {
        self.pack_old_and_dead_borrow_leaves(location)?;
        for created_location in self.ctxt.bc.twophase_borrow_activations(location) {
            let borrow = match self.pcg.borrow.graph().borrow_created_at(created_location) {
                Some(borrow) => borrow,
                None => continue,
            };
            let blocked_place = borrow.blocked_place.place();
            if self
                .pcg
                .borrow
                .graph()
                .contains(borrow.deref_place(self.ctxt), self.ctxt)
            {
                let upgrade_action = BorrowPCGAction::restore_capability(
                    borrow.deref_place(self.ctxt).place().into(),
                    CapabilityKind::Exclusive,
                );
                self.record_and_apply_action(upgrade_action.into())?;
            }
            if !blocked_place.is_owned(self.ctxt) {
                let actions = self.pcg.borrow.remove_read_permission_upwards(
                    blocked_place,
                    &mut self.pcg.capabilities,
                    self.ctxt,
                )?;
                self.actions.extend(actions.actions());
            }
            for place in blocked_place.iter_places(self.ctxt) {
                for rp in place.region_projections(self.ctxt).into_iter() {
                    if rp.is_nested_in_local_ty(self.ctxt) {
                        self.pcg.borrow.label_region_projection(
                            &rp.into(),
                            Some(location.into()),
                            self.ctxt,
                        );
                    }
                }
            }
        }
        Ok(())
    }
}

fn get_disjoint_lifetime_sets<'tcx, T: RegionProjectionBaseLike<'tcx>>(
    arg_region_projections: &[RegionProjection<'tcx, T>],
    ctxt: CompilerCtxt<'_, 'tcx>,
) -> Vec<FxHashSet<PcgRegion>> {
    let regions = arg_region_projections
        .iter()
        .map(|rp| rp.region(ctxt))
        .collect::<FxHashSet<_>>();
    let mut disjoin_lifetime_sets: Vec<FxHashSet<PcgRegion>> = vec![];
    for region in regions.iter() {
        let candidate = disjoin_lifetime_sets
            .iter_mut()
            .find(|ls| ctxt.bc.same_region(*region, *ls.iter().next().unwrap()));
        if let Some(ls) = candidate {
            ls.insert(*region);
        } else {
            disjoin_lifetime_sets.push(FxHashSet::from_iter([*region]));
        }
    }
    disjoin_lifetime_sets
}
