use crate::action::PcgAction;
use crate::borrow_pcg::action::{BorrowPCGAction, MakePlaceOldReason};
use crate::borrow_pcg::borrow_pcg_edge::{BorrowPcgEdge, BorrowPcgEdgeLike};
use crate::borrow_pcg::borrow_pcg_expansion::PlaceExpansion;
use crate::borrow_pcg::edge::kind::BorrowPcgEdgeKind;
use crate::borrow_pcg::edge::outlives::{BorrowFlowEdge, BorrowFlowEdgeKind};
use crate::borrow_pcg::region_projection::{PcgRegion, RegionProjection, RegionProjectionLabel};
use crate::free_pcs::{CapabilityKind, RepackOp};
use crate::pcg::triple::TripleWalker;
use crate::rustc_interface::middle::mir::{self, Location, Operand, Rvalue, Statement, Terminator};
use crate::utils::display::DisplayWithCompilerCtxt;
use crate::utils::validity::HasValidityCheck;
use crate::validity_assert_acyclic;

use crate::action::PcgActions;
use crate::utils::maybe_old::MaybeOldPlace;
use crate::utils::maybe_remote::MaybeRemotePlace;
use crate::utils::visitor::FallableVisitor;
use crate::utils::{self, CompilerCtxt, HasPlace, Place};

use super::{AnalysisObject, EvalStmtPhase, PCGUnsupportedError, Pcg, PcgError};

mod assign;
mod function_call;
mod obtain;
mod pack;
mod stmt;
mod triple;

pub(crate) struct PcgVisitor<'pcg, 'mir, 'tcx> {
    pcg: &'pcg mut Pcg<'tcx>,
    ctxt: CompilerCtxt<'mir, 'tcx>,
    actions: PcgActions<'tcx>,
    phase: EvalStmtPhase,
    tw: &'pcg TripleWalker<'mir, 'tcx>,
}

impl<'pcg, 'mir, 'tcx> PcgVisitor<'pcg, 'mir, 'tcx> {
    fn outlives(&self, sup: PcgRegion, sub: PcgRegion) -> bool {
        self.ctxt.bc.outlives(sup, sub)
    }

    fn connect_outliving_projections(
        &mut self,
        source_proj: RegionProjection<'tcx, MaybeOldPlace<'tcx>>,
        target: Place<'tcx>,
        _location: Location,
        kind: impl Fn(PcgRegion) -> BorrowFlowEdgeKind,
    ) -> Result<(), PcgError> {
        for target_proj in target.region_projections(self.ctxt).into_iter() {
            if self.outlives(source_proj.region(self.ctxt), target_proj.region(self.ctxt)) {
                self.record_and_apply_action(
                    BorrowPCGAction::add_edge(
                        BorrowPcgEdge::new(
                            BorrowFlowEdge::new(
                                source_proj.into(),
                                target_proj.into(),
                                kind(target_proj.region(self.ctxt)),
                                self.ctxt,
                            )
                            .into(),
                            self.pcg.borrow.path_conditions.clone(),
                        ),
                        true,
                    )
                    .into(),
                )?;
            }
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

impl<'tcx> FallableVisitor<'tcx> for PcgVisitor<'_, '_, 'tcx> {
    fn visit_statement_fallable(
        &mut self,
        statement: &Statement<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        self.perform_statement_actions(statement, location)
    }

    fn visit_operand_fallable(
        &mut self,
        operand: &Operand<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        self.super_operand_fallable(operand, location)?;
        if self.phase == EvalStmtPhase::PostMain
            && let Operand::Move(place) = operand
        {
            let place: utils::Place<'tcx> = (*place).into();
            self.record_and_apply_action(
                BorrowPCGAction::make_place_old(place, MakePlaceOldReason::MoveOut).into(),
            )?;
        }
        Ok(())
    }

    fn visit_terminator_fallable(
        &mut self,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        self.pcg.assert_validity(self.ctxt);
        validity_assert_acyclic(self.pcg, location, self.ctxt);
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
        if matches!(rvalue, Rvalue::Ref(_, mir::BorrowKind::Fake(_), _)) {
            return Ok(());
        }
        self.super_rvalue_fallable(rvalue, location)?;
        Ok(())
    }
}
impl<'tcx> PcgVisitor<'_, '_, 'tcx> {
    pub(crate) fn apply(
        mut self,
        object: AnalysisObject<'_, 'tcx>,
        location: Location,
    ) -> Result<PcgActions<'tcx>, PcgError> {
        match self.phase {
            EvalStmtPhase::PreOperands => {
                self.perform_borrow_initial_pre_operand_actions(location)?;
                self.collapse_owned_places()?;
                for triple in self.tw.operand_triples.iter() {
                    self.require_triple(*triple, location)?;
                }
            }
            EvalStmtPhase::PostOperands => {
                for triple in self.tw.operand_triples.iter() {
                    self.ensure_triple(*triple)?;
                }
            }
            EvalStmtPhase::PreMain => {
                for triple in self.tw.main_triples.iter() {
                    self.require_triple(*triple, location)?;
                }
            }
            EvalStmtPhase::PostMain => {
                for triple in self.tw.main_triples.iter() {
                    self.ensure_triple(*triple)?;
                }
            }
        }
        match object {
            AnalysisObject::Statement(statement) => {
                self.visit_statement_fallable(statement, location)?
            }
            AnalysisObject::Terminator(terminator) => {
                self.visit_terminator_fallable(terminator, location)?
            }
        }
        validity_assert_acyclic(self.pcg, location, self.ctxt);
        Ok(self.actions)
    }
    #[tracing::instrument(skip(self, edge, location))]
    pub(crate) fn remove_edge_and_set_latest(
        &mut self,
        edge: impl BorrowPcgEdgeLike<'tcx>,
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
            if let Some(place) = node.as_current_place() {
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

        if let BorrowPcgEdgeKind::BorrowPcgExpansion(expansion) = edge.kind() {
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
                    if !matches!(to_redirect, BorrowPcgEdgeKind::BorrowPcgExpansion(_)) {
                        self.pcg.borrow.graph.redirect_edge(
                            to_redirect,
                            *node,
                            expansion.base,
                            self.ctxt,
                        )
                    }
                }
            }
        }
        Ok(())
    }

    #[tracing::instrument(skip(self))]
    fn record_and_apply_action(&mut self, action: PcgAction<'tcx>) -> Result<bool, PcgError> {
        let result =
            match &action {
                PcgAction::Borrow(action) => self.pcg.borrow.apply_action(
                    action.clone(),
                    &mut self.pcg.capabilities,
                    self.ctxt,
                )?,
                PcgAction::Owned(action) => match action {
                    RepackOp::RegainLoanedCapability(place, capability_kind) => self
                        .pcg
                        .capabilities
                        .insert((*place).into(), *capability_kind),
                    RepackOp::Expand(from, to, capability) => {
                        let target_places = from.expand_one_level(*to, self.ctxt)?.expansion();
                        let capability_projections =
                            self.pcg.owned.locals_mut()[from.local].get_allocated_mut();
                        capability_projections.insert_expansion(
                            *from,
                            PlaceExpansion::from_places(target_places.clone(), self.ctxt),
                        );
                        for target_place in target_places {
                            self.pcg
                                .capabilities
                                .insert(target_place.into(), *capability);
                        }
                        if capability.is_read() {
                            self.pcg
                                .capabilities
                                .insert((*from).into(), CapabilityKind::Read);
                        } else {
                            self.pcg.capabilities.remove((*from).into());
                        }
                        true
                    }
                    RepackOp::DerefShallowInit(from, to) => {
                        let target_places = from.expand_one_level(*to, self.ctxt)?.expansion();
                        let capability_projections =
                            self.pcg.owned.locals_mut()[from.local].get_allocated_mut();
                        capability_projections.insert_expansion(
                            *from,
                            PlaceExpansion::from_places(target_places.clone(), self.ctxt),
                        );
                        for target_place in target_places {
                            self.pcg
                                .capabilities
                                .insert(target_place.into(), CapabilityKind::Read);
                        }
                        true
                    }
                    RepackOp::Collapse(base_place, proj_place, _) => {
                        let capability_projections =
                            self.pcg.owned.locals_mut()[base_place.local].get_allocated_mut();
                        let expansion_places = base_place
                            .expand_one_level(*proj_place, self.ctxt)?
                            .expansion();
                        let retained_cap = expansion_places.iter().fold(
                            CapabilityKind::Exclusive,
                            |acc, place| match self.pcg.capabilities.remove((*place).into()) {
                                Some(cap) => acc.minimum(cap).unwrap_or(CapabilityKind::Write),
                                None => acc,
                            },
                        );
                        self.pcg
                            .capabilities
                            .insert((*base_place).into(), retained_cap);
                        capability_projections.expansions.remove(base_place);
                        true
                    }
                    _ => unreachable!(),
                },
            };
        self.actions.push(action);
        Ok(result)
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
            tracing::debug!(
                "activate twophase borrow: {}",
                borrow.to_short_string(self.ctxt)
            );
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
                self.remove_read_permission_upwards(blocked_place)?;
            }
            for place in blocked_place.iter_places(self.ctxt) {
                for rp in place.region_projections(self.ctxt).into_iter() {
                    if rp.is_nested_under_mut_ref(self.ctxt) {
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
