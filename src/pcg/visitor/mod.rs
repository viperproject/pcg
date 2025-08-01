use itertools::Itertools;

use crate::action::{BorrowPcgAction, PcgAction};
use crate::borrow_pcg::action::LabelPlaceReason;
use crate::borrow_pcg::borrow_pcg_edge::BorrowPcgEdge;
use crate::borrow_pcg::borrow_pcg_expansion::PlaceExpansion;
use crate::borrow_pcg::edge::kind::BorrowPcgEdgeKind;
use crate::borrow_pcg::edge::outlives::{BorrowFlowEdge, BorrowFlowEdgeKind};
use crate::borrow_pcg::region_projection::{LifetimeProjection, PcgRegion};
use crate::free_pcs::{CapabilityKind, FreePlaceCapabilitySummary, RepackExpand};
use crate::pcg::obtain::{PlaceExpander, PlaceObtainer};
use crate::pcg::place_capabilities::{PlaceCapabilities, PlaceCapabilitiesInterface};
use crate::pcg::triple::TripleWalker;
use crate::pcg::{PcgDebugData, PcgMutRefLike};
use crate::pcg_validity_assert;
use crate::rustc_interface::middle::mir::{self, Location, Operand, Rvalue, Statement, Terminator};
use crate::utils::data_structures::HashSet;
use crate::utils::display::DisplayWithCompilerCtxt;

use crate::action::PcgActions;
use crate::utils::maybe_old::MaybeLabelledPlace;
use crate::utils::visitor::FallableVisitor;
use crate::utils::{self, AnalysisLocation, CompilerCtxt, HasPlace, Place};

use super::{
    AnalysisObject, EvalStmtPhase, PCGNode, PCGNodeLike, Pcg, PcgError, PcgUnsupportedError,
};

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
    analysis_location: AnalysisLocation,
    tw: &'pcg TripleWalker<'mir, 'tcx>,
    debug_data: Option<PcgDebugData>,
}

impl<'pcg, 'mir, 'tcx> PcgVisitor<'pcg, 'mir, 'tcx> {
    fn phase(&self) -> EvalStmtPhase {
        self.analysis_location.eval_stmt_phase
    }

    fn location(&self) -> Location {
        self.analysis_location.location
    }

    fn outlives(&self, sup: PcgRegion, sub: PcgRegion) -> bool {
        self.ctxt.bc.outlives(sup, sub, self.location())
    }

    fn connect_outliving_projections(
        &mut self,
        source_proj: LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>>,
        target: Place<'tcx>,
        kind: impl Fn(PcgRegion) -> BorrowFlowEdgeKind,
    ) -> Result<(), PcgError> {
        for target_proj in target.region_projections(self.ctxt).into_iter() {
            if self.outlives(source_proj.region(self.ctxt), target_proj.region(self.ctxt)) {
                self.record_and_apply_action(
                    BorrowPcgAction::add_edge(
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
                        "connect_outliving_projections",
                        self.ctxt,
                    )
                    .into(),
                )?;
            }
        }
        Ok(())
    }

    pub(crate) fn visit(
        pcg: &'pcg mut Pcg<'tcx>,
        ctxt: CompilerCtxt<'mir, 'tcx>,
        tw: &'pcg TripleWalker<'mir, 'tcx>,
        analysis_location: AnalysisLocation,
        analysis_object: AnalysisObject<'_, 'tcx>,
        debug_data: Option<PcgDebugData>,
    ) -> Result<PcgActions<'tcx>, PcgError> {
        let visitor = Self::new(pcg, ctxt, tw, analysis_location, debug_data);
        let actions = visitor.apply(analysis_object)?;
        Ok(actions)
    }

    pub(crate) fn new(
        pcg: &'pcg mut Pcg<'tcx>,
        ctxt: CompilerCtxt<'mir, 'tcx>,
        tw: &'pcg TripleWalker<'mir, 'tcx>,
        analysis_location: AnalysisLocation,
        debug_data: Option<PcgDebugData>,
    ) -> Self {
        Self {
            pcg,
            ctxt,
            actions: PcgActions::default(),
            analysis_location,
            tw,
            debug_data,
        }
    }
}

impl<'tcx> FallableVisitor<'tcx> for PcgVisitor<'_, '_, 'tcx> {
    #[tracing::instrument(skip(self))]
    fn visit_statement_fallable(
        &mut self,
        statement: &Statement<'tcx>,
        _location: Location,
    ) -> Result<(), PcgError> {
        self.perform_statement_actions(statement)?;
        Ok(())
    }

    fn visit_operand_fallable(
        &mut self,
        operand: &Operand<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        match operand {
            Operand::Copy(place) => {
                let place: Place<'tcx> = (*place).into();
                if place.has_lifetimes_under_unsafe_ptr(self.ctxt) {
                    return Err(PcgError::unsupported(
                        PcgUnsupportedError::MoveUnsafePtrWithNestedLifetime,
                    ));
                }
            }
            Operand::Move(place) => {
                if self.phase() == EvalStmtPhase::PostOperands {
                    let snapshot_location = self.place_obtainer().prev_snapshot_location();
                    self.record_and_apply_action(
                        BorrowPcgAction::make_place_old(
                            (*place).into(),
                            snapshot_location,
                            LabelPlaceReason::MoveOut,
                        )
                        .into(),
                    )?;
                }
            }
            _ => {}
        }
        self.super_operand_fallable(operand, location)?;
        Ok(())
    }

    fn visit_terminator_fallable(
        &mut self,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        self.super_terminator_fallable(terminator, location)?;
        if self.phase() == EvalStmtPhase::PostMain
            && let mir::TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } = &terminator.kind
        {
            for operand in args {
                if let Some(place) = operand.node.place() {
                    let place: utils::Place<'tcx> = place.into();
                    if place.has_lifetimes_under_unsafe_ptr(self.ctxt) {
                        return Err(PcgUnsupportedError::CallWithUnsafePtrWithNestedLifetime.into());
                    }
                }
            }
            let destination: utils::Place<'tcx> = (*destination).into();
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
            tracing::error!("DerefUnsafePtr: {}", place.to_short_string(self.ctxt));
            return Err(PcgError::unsupported(PcgUnsupportedError::DerefUnsafePtr));
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

impl<'state, 'mir: 'state> PlaceObtainer<'state, 'mir, '_> {
    pub(crate) fn collapse_owned_places(&mut self) -> Result<(), PcgError> {
        let ctxt = self.ctxt;
        for caps in self.pcg.owned.data.clone().unwrap().expansions() {
            let mut expansions = caps
                .expansions()
                .clone()
                .into_iter()
                .sorted_by_key(|pe| pe.place.projection().len())
                .collect::<Vec<_>>();
            while let Some(pe) = expansions.pop() {
                let expansion_places = pe.expansion_places(ctxt);
                let base = pe.place;
                if expansion_places
                    .iter()
                    .all(|p| !self.pcg.borrow.graph.contains(*p, ctxt))
                    && let Some(candidate_cap) = self
                        .pcg
                        .capabilities
                        .get(pe.arbitrary_expansion_place(ctxt))
                    && expansion_places
                        .iter()
                        .all(|p| self.pcg.capabilities.get(*p) == Some(candidate_cap))
                {
                    self.collapse(
                        pe.place,
                        candidate_cap,
                        format!("Collapse owned place {}", base.to_short_string(self.ctxt)),
                    )?;
                    if pe.place.projection.is_empty()
                        && self.pcg.capabilities.get(pe.place) == Some(CapabilityKind::Read)
                    {
                        self.pcg
                            .capabilities
                            .insert(base, CapabilityKind::Exclusive, self.ctxt);
                    }
                }
            }
        }
        Ok(())
    }
}

impl<'tcx> PcgVisitor<'_, '_, 'tcx> {
    pub(crate) fn apply(
        mut self,
        object: AnalysisObject<'_, 'tcx>,
    ) -> Result<PcgActions<'tcx>, PcgError> {
        match self.phase() {
            EvalStmtPhase::PreOperands => {
                self.perform_borrow_initial_pre_operand_actions()?;
                self.place_obtainer().collapse_owned_places()?;
                for triple in self.tw.operand_triples.iter() {
                    tracing::debug!("Require triple {:?}", triple);
                    self.require_triple(*triple)?;
                }
            }
            EvalStmtPhase::PostOperands => {
                for triple in self.tw.operand_triples.iter() {
                    self.ensure_triple(*triple)?;
                }
            }
            EvalStmtPhase::PreMain => {
                for triple in self.tw.main_triples.iter() {
                    tracing::debug!("Require triple {:?}", triple);
                    self.require_triple(*triple)?;
                }
            }
            EvalStmtPhase::PostMain => {
                for triple in self.tw.main_triples.iter() {
                    self.ensure_triple(*triple)?;
                }
            }
        }
        let location = self.location();
        match object {
            AnalysisObject::Statement(statement) => {
                self.visit_statement_fallable(statement, location)?
            }
            AnalysisObject::Terminator(terminator) => {
                self.visit_terminator_fallable(terminator, location)?
            }
        }
        if self.phase() == EvalStmtPhase::PostMain {
            self.pcg
                .as_mut_ref()
                .assert_validity_at_location(self.ctxt, location);
        }
        Ok(self.actions)
    }

    #[allow(unused)]
    fn any_reachable_reverse(
        &self,
        node: PCGNode<'tcx>,
        predicate: impl Fn(&PCGNode<'tcx>) -> bool,
    ) -> bool {
        let mut stack = vec![node];
        let mut seen = HashSet::default();
        while let Some(node) = stack.pop() {
            if seen.contains(&node) {
                continue;
            }
            seen.insert(node);
            if predicate(&node) {
                return true;
            }
            if let Some(local_node) = node.try_to_local_node(self.ctxt) {
                let blocked_by = self
                    .pcg
                    .borrow
                    .graph()
                    .nodes_blocked_by(local_node, self.ctxt);
                for node in blocked_by {
                    if !seen.contains(&node) {
                        stack.push(node);
                    }
                }
            }
        }
        false
    }

    fn activate_twophase_borrow_created_at(
        &mut self,
        created_location: Location,
    ) -> Result<(), PcgError> {
        let borrow = match self.pcg.borrow.graph().borrow_created_at(created_location) {
            Some(borrow) => borrow,
            None => return Ok(()),
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
            let upgrade_action = BorrowPcgAction::restore_capability(
                borrow.deref_place(self.ctxt).place(),
                CapabilityKind::Exclusive,
                "perform_borrow_initial_pre_operand_actions",
            );
            self.record_and_apply_action(upgrade_action.into())?;
        }
        if !blocked_place.is_owned(self.ctxt) {
            self.place_obtainer()
                .remove_read_permission_upwards_and_label_rps(
                    blocked_place,
                    "Activate twophase borrow",
                )?;
        }
        Ok(())
    }

    fn perform_borrow_initial_pre_operand_actions(&mut self) -> Result<(), PcgError> {
        self.place_obtainer()
            .pack_old_and_dead_borrow_leaves(None)?;
        for created_location in self.ctxt.bc.twophase_borrow_activations(self.location()) {
            self.activate_twophase_borrow_created_at(created_location)?;
        }
        let frozen_graph = self.pcg.borrow.graph.frozen_graph();
        let leaf_nodes = frozen_graph.leaf_nodes(self.ctxt);
        let leaf_future_node_places = leaf_nodes
            .iter()
            .filter_map(|node| match node {
                PCGNode::Place(_) => None,
                PCGNode::LifetimeProjection(region_projection) => {
                    if region_projection.is_placeholder() {
                        region_projection.base.as_current_place()
                    } else {
                        None
                    }
                }
            })
            .collect::<HashSet<_>>();
        for place in leaf_future_node_places {
            // If the place has become a leaf, and its not borrowed, then we remove the future label
            if self
                .pcg
                .borrow
                .graph()
                .edges_blocking(place.into(), self.ctxt)
                .all(|e| !matches!(e.kind, BorrowPcgEdgeKind::BorrowPcgExpansion(_)))
                && !self
                    .ctxt
                    .bc
                    .is_directly_blocked(place, self.location(), self.ctxt)
            {
                let action = PcgAction::restore_capability(
                    place,
                    CapabilityKind::Exclusive,
                    "Leaf future node restore cap",
                    self.ctxt,
                );
                self.record_and_apply_action(action)?;
            }
        }
        Ok(())
    }
}

impl<'tcx> FreePlaceCapabilitySummary<'tcx> {
    pub(crate) fn perform_expand_action(
        &mut self,
        expand: RepackExpand<'tcx>,
        capabilities: &mut PlaceCapabilities<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<(), PcgError> {
        let expansions = self.locals_mut()[expand.local()].get_allocated_mut();
        expansions.perform_expand_action(expand, capabilities, ctxt)
    }
}
