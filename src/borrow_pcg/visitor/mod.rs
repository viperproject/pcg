use crate::{
    action::PcgActions,
    free_pcs::FreePlaceCapabilitySummary,
    pcg::{place_capabilities::PlaceCapabilities, EvalStmtPhase},
    utils::visitor::FallableVisitor,
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
    action::BorrowPCGAction,
    borrow_pcg_edge::BorrowPCGEdge,
    edge::outlives::{BorrowFlowEdge, BorrowFlowEdgeKind},
    path_condition::PathConditions,
    region_projection::{PcgRegion, RegionIdx, RegionProjection},
    state::BorrowsState,
};
use crate::borrow_pcg::action::executed_actions::ExecutedActions;
use crate::borrow_pcg::state::obtain::ObtainReason;
use crate::utils::place::maybe_old::MaybeOldPlace;
use crate::utils::{self, CompilerCtxt};

mod function_call;
mod stmt;

pub(crate) struct BorrowsVisitor<'tcx, 'mir, 'state> {
    pub(super) ctxt: CompilerCtxt<'mir, 'tcx>,
    pub(super) actions: PcgActions<'tcx>,
    state: &'state mut BorrowsState<'tcx>,
    capabilities: &'state mut PlaceCapabilities<'tcx>,
    owned: &'state FreePlaceCapabilitySummary<'tcx>,
    phase: EvalStmtPhase,
}

impl<'tcx, 'mir, 'state> BorrowsVisitor<'tcx, 'mir, 'state> {
    fn record_actions(&mut self, actions: ExecutedActions<'tcx>) {
        self.actions.extend(actions.actions());
    }

    fn apply_action(&mut self, action: BorrowPCGAction<'tcx>) -> bool {
        self.actions.push(action.clone().into());
        self.state
            .apply_action(action, self.capabilities, self.ctxt)
            .unwrap()
    }

    pub(super) fn new(
        ctxt: CompilerCtxt<'mir, 'tcx>,
        state: &'state mut BorrowsState<'tcx>,
        capabilities: &'state mut PlaceCapabilities<'tcx>,
        owned: &'state FreePlaceCapabilitySummary<'tcx>,
        phase: EvalStmtPhase,
    ) -> BorrowsVisitor<'tcx, 'mir, 'state> {
        BorrowsVisitor {
            ctxt,
            actions: PcgActions::default(),
            state,
            capabilities,
            owned,
            phase,
        }
    }

    fn connect_outliving_projections(
        &mut self,
        source_proj: RegionProjection<'tcx, MaybeOldPlace<'tcx>>,
        target: Place<'tcx>,
        location: Location,
        kind: impl Fn(PcgRegion) -> BorrowFlowEdgeKind,
    ) {
        for target_proj in target.region_projections(self.ctxt).into_iter() {
            if self.outlives(source_proj.region(self.ctxt), target_proj.region(self.ctxt)) {
                self.apply_action(BorrowPCGAction::add_edge(
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
                ));
            }
        }
    }

    fn outlives(&self, sup: PcgRegion, sub: PcgRegion) -> bool {
        self.ctxt.bc.outlives(sup, sub)
    }
}

impl BorrowsVisitor<'_, '_, '_> {}

impl<'tcx> FallableVisitor<'tcx> for BorrowsVisitor<'tcx, '_, '_> {
    fn visit_operand_fallable(
        &mut self,
        operand: &Operand<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        Ok(())
    }

    #[tracing::instrument(skip(self, terminator))]
    fn visit_terminator_fallable(
        &mut self,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
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
        self.super_statement_fallable(statement, location)?;

        match self.phase {
            EvalStmtPhase::PreOperands => {
                if let StatementKind::FakeRead(box (_, place)) = &statement.kind {
                    let place: utils::Place<'tcx> = (*place).into();
                    if !place.is_owned(self.ctxt) {
                        let expansion_reason = ObtainReason::FakeRead;
                        let expansion_actions = self.state.obtain(
                            self.ctxt,
                            place,
                            self.capabilities,
                            self.owned,
                            location,
                            expansion_reason,
                        )?;
                        self.record_actions(expansion_actions);
                    }
                }
            }
            EvalStmtPhase::PreMain => {
                unreachable!()
            }
            EvalStmtPhase::PostMain => {
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
                            this.ctxt,
                            place.into(),
                            this.capabilities,
                            this.owned,
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
pub(crate) fn extract_regions<'tcx, C: Copy>(
    ty: ty::Ty<'tcx>,
    repacker: CompilerCtxt<'_, 'tcx, C>,
) -> IndexVec<RegionIdx, PcgRegion> {
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
    repacker: CompilerCtxt<'_, 'tcx>,
) -> IndexVec<RegionIdx, PcgRegion> {
    if let ty::TyKind::Ref(_, ty, _) = ty.kind() {
        extract_regions(*ty, repacker)
    } else {
        extract_regions(ty, repacker)
    }
}
