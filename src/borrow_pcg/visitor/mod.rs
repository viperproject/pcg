use std::rc::Rc;

use crate::{
    pcg::EvalStmtPhase,
    utils::{visitor::FallableVisitor, HasPlace},
};
use tracing::instrument;

use crate::{
    pcg::{PCGUnsupportedError, PcgError},
    rustc_interface::{
        index::IndexVec,
        middle::{
            mir::{
                self, BorrowKind, Location, Operand, Rvalue, Statement, StatementKind, Terminator,
                TerminatorKind,
            },
            ty::{self, TypeSuperVisitable, TypeVisitable, TypeVisitor},
        },
    },
    utils::Place,
};

use super::{
    action::{BorrowPCGAction, MakePlaceOldReason},
    borrow_pcg_edge::BorrowPCGEdge,
    coupling_graph_constructor::BorrowCheckerInterface,
    edge::outlives::{OutlivesEdge, OutlivesEdgeKind},
    path_condition::PathConditions,
    region_projection::{PCGRegion, RegionIdx, RegionProjection},
    state::BorrowsState,
};
use super::{domain::AbstractionOutputTarget, engine::BorrowsEngine};
use crate::borrow_pcg::action::actions::BorrowPCGActions;
use crate::borrow_pcg::action::executed_actions::ExecutedActions;
use crate::borrow_pcg::state::obtain::ObtainReason;
use crate::utils::place::maybe_old::MaybeOldPlace;
use crate::{
    free_pcs::CapabilityKind,
    utils::{self, PlaceRepacker},
};

mod function_call;
mod stmt;

pub(crate) struct BorrowsVisitor<'tcx, 'mir, 'state> {
    pub(super) repacker: PlaceRepacker<'mir, 'tcx>,
    pub(super) actions: BorrowPCGActions<'tcx>,
    state: &'state mut BorrowsState<'tcx>,
    bc: Rc<dyn BorrowCheckerInterface<'mir, 'tcx> + 'mir>,
    phase: EvalStmtPhase,
}

impl<'tcx, 'mir, 'state> BorrowsVisitor<'tcx, 'mir, 'state> {
    fn record_actions(&mut self, actions: ExecutedActions<'tcx>) {
        self.actions.extend(actions.actions());
    }

    fn apply_action(&mut self, action: BorrowPCGAction<'tcx>) -> bool {
        self.actions.push(action.clone());
        self.state.apply_action(action, self.repacker).unwrap()
    }

    pub(super) fn new(
        engine: &BorrowsEngine<'mir, 'tcx>,
        state: &'state mut BorrowsState<'tcx>,
        bc: Rc<dyn BorrowCheckerInterface<'mir, 'tcx> + 'mir>,
        phase: EvalStmtPhase,
    ) -> BorrowsVisitor<'tcx, 'mir, 'state> {
        BorrowsVisitor {
            repacker: PlaceRepacker::new(engine.body, engine.tcx),
            actions: BorrowPCGActions::new(),
            state,
            bc,
            phase,
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
        self.bc.outlives(sup, sub)
    }

    fn projections_borrowing_from_input_lifetime(
        &self,
        input_lifetime: PCGRegion,
        output_place: utils::Place<'tcx>,
    ) -> Vec<AbstractionOutputTarget<'tcx>> {
        let mut result = vec![];
        let output_ty = output_place.ty(self.repacker).ty;
        for (output_lifetime_idx, output_lifetime) in
            extract_regions(output_ty, self.repacker).into_iter_enumerated()
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

impl BorrowsVisitor<'_, '_, '_> {
    fn perform_base_pre_operand_actions(&mut self, location: Location) -> Result<(), PcgError> {
        let actions =
            self.state
                .pack_old_and_dead_leaves(self.repacker, location, self.bc.as_ref())?;
        self.record_actions(actions);
        for created_location in self.bc.twophase_borrow_activations(location) {
            let borrow = match self.state.graph().borrow_created_at(created_location) {
                Some(borrow) => borrow,
                None => continue,
            };
            let blocked_place = borrow.blocked_place.place();
            if self
                .state
                .graph()
                .contains(borrow.deref_place(self.repacker), self.repacker)
            {
                let upgrade_action = BorrowPCGAction::restore_capability(
                    borrow.deref_place(self.repacker).place().into(),
                    CapabilityKind::Exclusive,
                );
                self.apply_action(upgrade_action);
            }
            if !blocked_place.is_owned(self.repacker) {
                let actions = self
                    .state
                    .remove_read_permission_upwards(blocked_place, self.repacker)?;
                self.record_actions(actions);
            }
        }
        Ok(())
    }
}

impl<'tcx> FallableVisitor<'tcx> for BorrowsVisitor<'tcx, '_, '_> {
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
                    let expansion_actions =
                        self.state
                            .obtain(self.repacker, place, location, expansion_reason)?;
                    self.record_actions(expansion_actions);
                }
                _ => {}
            },
            EvalStmtPhase::PostOperands => {
                if let Operand::Move(place) = operand {
                    let place: utils::Place<'tcx> = (*place).into();
                    if !place.is_owned(self.repacker) {
                        self.state.set_capability(
                            place.into(),
                            CapabilityKind::Write,
                            self.repacker,
                        );
                    }
                }
            }
            EvalStmtPhase::PostMain => {
                if let Operand::Move(place) = operand {
                    let place: utils::Place<'tcx> = (*place).into();
                    self.apply_action(BorrowPCGAction::make_place_old(
                        place,
                        MakePlaceOldReason::MoveOut,
                    ));
                }
            }
            _ => {}
        }
        Ok(())
    }

    #[tracing::instrument(skip(self, terminator))]
    fn visit_terminator_fallable(
        &mut self,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        if self.phase == EvalStmtPhase::PreOperands {
            self.perform_base_pre_operand_actions(location)?;
        }
        self.super_terminator_fallable(terminator, location)?;
        if self.phase == EvalStmtPhase::PostMain
            && let TerminatorKind::Call {
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
            self.make_function_call_abstraction(
                func,
                &args.iter().map(|arg| &arg.node).collect::<Vec<_>>(),
                destination,
                location,
            )?;
        }
        Ok(())
    }

    #[tracing::instrument(skip(self))]
    fn visit_statement_fallable(
        &mut self,
        statement: &Statement<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        if self.phase == EvalStmtPhase::PreOperands {
            self.perform_base_pre_operand_actions(location)?;
        }

        self.super_statement_fallable(statement, location)?;

        match self.phase {
            EvalStmtPhase::PreOperands => {
                if let StatementKind::FakeRead(box (_, place)) = &statement.kind {
                    let place: utils::Place<'tcx> = (*place).into();
                    if !place.is_owned(self.repacker) {
                        let expansion_reason = ObtainReason::FakeRead;
                        let expansion_actions =
                            self.state
                                .obtain(self.repacker, place, location, expansion_reason)?;
                        self.record_actions(expansion_actions);
                    }
                }
            }
            EvalStmtPhase::PreMain => {
                self.stmt_pre_main(statement, location)?;
            }
            EvalStmtPhase::PostMain => {
                self.stmt_post_main(statement, location)?;
            }
            _ => {}
        }
        Ok(())
    }

    fn visit_place_fallable(
        &mut self,
        place: Place<'tcx>,
        _context: mir::visit::PlaceContext,
        _location: mir::Location,
    ) -> Result<(), PcgError> {
        if place.contains_unsafe_deref(self.repacker) {
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
            this: &mut BorrowsVisitor<'tcx, 'mir, 'state>,
            rvalue: &Rvalue<'tcx>,
            location: Location,
        ) -> Result<(), PcgError> {
            if matches!(rvalue, Rvalue::Ref(_, BorrowKind::Fake(_), _)) {
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
                        let expansion_actions = this.state.obtain(
                            this.repacker,
                            place.into(),
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

struct LifetimeExtractor<'tcx> {
    lifetimes: Vec<ty::Region<'tcx>>,
    #[allow(dead_code)]
    tcx: ty::TyCtxt<'tcx>,
}

impl<'tcx> TypeVisitor<ty::TyCtxt<'tcx>> for LifetimeExtractor<'tcx> {
    fn visit_ty(&mut self, ty: ty::Ty<'tcx>) {
        match ty.kind() {
            ty::TyKind::Closure(_, args) => {
                let closure_args = args.as_closure();
                let upvar_tys = closure_args.upvar_tys();
                for ty in upvar_tys.iter() {
                    self.visit_ty(ty);
                }
            }
            _ => {
                ty.super_visit_with(self);
            }
        }
    }
    fn visit_region(&mut self, rr: ty::Region<'tcx>) {
        if !self.lifetimes.contains(&rr) {
            self.lifetimes.push(rr);
        }
    }
}

/// Returns all of the (possibly nested) regions in `ty` that could be part of
/// its region projection. In particular, the intention of this function is to
/// *only* return regions that correspond to data borrowed in a type. In
/// particular, for closures / functions, we do not include regions in the input
/// or argument types.
/// If this type is a reference type, e.g. `&'a mut T`, then this will return
/// `'a` and the regions within `T`.
///
/// The resulting list does not contain duplicates, e.g. T<'a, 'a> will return
/// `['a]`. Note that the order of the returned regions is arbitrary, but
/// consistent between calls to types with the same "shape". E.g T<'a, 'b> and
/// T<'c, 'd> will return the same list of regions will return `['a, 'b]` and
/// `['c, 'd]` respectively. This enables substitution of regions to handle
/// moves in the PCG e.g for the statement `let x: T<'a, 'b> = move c: T<'c,
/// 'd>`.
pub(crate) fn extract_regions<'tcx>(
    ty: ty::Ty<'tcx>,
    repacker: PlaceRepacker<'_, 'tcx>,
) -> IndexVec<RegionIdx, PCGRegion> {
    let mut visitor = LifetimeExtractor {
        lifetimes: vec![],
        tcx: repacker.tcx(),
    };
    ty.visit_with(&mut visitor);
    IndexVec::from_iter(visitor.lifetimes.iter().map(|r| (*r).into()))
}

#[allow(unused)]
pub(crate) fn extract_inner_regions<'tcx>(
    ty: ty::Ty<'tcx>,
    repacker: PlaceRepacker<'_, 'tcx>,
) -> IndexVec<RegionIdx, PCGRegion> {
    if let ty::TyKind::Ref(_, ty, _) = ty.kind() {
        extract_regions(*ty, repacker)
    } else {
        extract_regions(ty, repacker)
    }
}
