use itertools::Itertools;

use crate::action::{BorrowPcgAction, PcgAction};
use crate::borrow_pcg::action::MakePlaceOldReason;
use crate::borrow_pcg::borrow_pcg_edge::{BorrowPcgEdge, BorrowPcgEdgeLike};
use crate::borrow_pcg::borrow_pcg_expansion::{BorrowPcgExpansion, PlaceExpansion};
use crate::borrow_pcg::edge::kind::BorrowPcgEdgeKind;
use crate::borrow_pcg::edge::outlives::{BorrowFlowEdge, BorrowFlowEdgeKind};
use crate::borrow_pcg::edge_data::LabelPlacePredicate;
use crate::borrow_pcg::has_pcs_elem::{LabelPlace, SetLabel};
use crate::borrow_pcg::region_projection::{
    LocalRegionProjection, PcgRegion, RegionProjection, RegionProjectionLabel,
};
use crate::free_pcs::{CapabilityKind, FreePlaceCapabilitySummary, RepackExpand, RepackOp};
use crate::pcg::dot_graphs::{generate_dot_graph, ToGraph};
use crate::pcg::place_capabilities::{PlaceCapabilities, PlaceCapabilitiesInterface};
use crate::pcg::triple::TripleWalker;
use crate::pcg::PcgDebugData;
use crate::pcg_validity_assert;
use crate::rustc_interface::middle::mir::{self, Location, Operand, Rvalue, Statement, Terminator};
use crate::utils::data_structures::HashSet;
use crate::utils::display::DisplayWithCompilerCtxt;

use crate::action::PcgActions;
use crate::utils::maybe_old::MaybeOldPlace;
use crate::utils::visitor::FallableVisitor;
use crate::utils::{self, CompilerCtxt, HasPlace, Place, SnapshotLocation};

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
    phase: EvalStmtPhase,
    tw: &'pcg TripleWalker<'mir, 'tcx>,
    location: Location,
    debug_data: Option<PcgDebugData>,
}

impl<'pcg, 'mir, 'tcx> PcgVisitor<'pcg, 'mir, 'tcx> {
    fn outlives(&self, sup: PcgRegion, sub: PcgRegion) -> bool {
        self.ctxt.bc.outlives(sup, sub)
    }

    fn connect_outliving_projections(
        &mut self,
        source_proj: RegionProjection<'tcx, MaybeOldPlace<'tcx>>,
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
                        false,
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
        phase: EvalStmtPhase,
        analysis_object: AnalysisObject<'_, 'tcx>,
        location: Location,
        debug_data: Option<PcgDebugData>,
    ) -> Result<PcgActions<'tcx>, PcgError> {
        let visitor = Self::new(pcg, ctxt, tw, phase, location, debug_data);
        let actions = visitor.apply(analysis_object)?;
        Ok(actions)
    }

    pub(crate) fn new(
        pcg: &'pcg mut Pcg<'tcx>,
        ctxt: CompilerCtxt<'mir, 'tcx>,
        tw: &'pcg TripleWalker<'mir, 'tcx>,
        phase: EvalStmtPhase,
        location: Location,
        debug_data: Option<PcgDebugData>,
    ) -> Self {
        Self {
            pcg,
            ctxt,
            actions: PcgActions::default(),
            phase,
            tw,
            location,
            debug_data,
        }
    }
}

impl<'tcx> FallableVisitor<'tcx> for PcgVisitor<'_, '_, 'tcx> {
    #[tracing::instrument(skip(self, location))]
    fn visit_statement_fallable(
        &mut self,
        statement: &Statement<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        self.perform_statement_actions(statement)?;
        self.pcg.assert_validity_at_location(self.ctxt, location);
        Ok(())
    }

    fn visit_operand_fallable(
        &mut self,
        operand: &Operand<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        if let Operand::Copy(place) = operand {
            let place: Place<'tcx> = (*place).into();
            if place.has_lifetimes_under_unsafe_ptr(self.ctxt) {
                return Err(PcgError::unsupported(
                    PcgUnsupportedError::MoveUnsafePtrWithNestedLifetime,
                ));
            }
        }
        self.super_operand_fallable(operand, location)?;
        if self.phase == EvalStmtPhase::PostMain
            && let Operand::Move(place) = operand
        {
            self.record_and_apply_action(
                BorrowPcgAction::make_place_old((*place).into(), MakePlaceOldReason::MoveOut)
                    .into(),
            )?;
        }
        Ok(())
    }

    fn visit_terminator_fallable(
        &mut self,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        self.pcg.assert_validity_at_location(self.ctxt, location);
        self.super_terminator_fallable(terminator, location)?;
        if self.phase == EvalStmtPhase::PostMain
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
            self.record_and_apply_action(
                BorrowPcgAction::set_latest(
                    destination,
                    SnapshotLocation::After(location),
                    "Destination of Function Call",
                )
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
impl<'tcx> PcgVisitor<'_, '_, 'tcx> {
    pub(crate) fn apply(
        mut self,
        object: AnalysisObject<'_, 'tcx>,
    ) -> Result<PcgActions<'tcx>, PcgError> {
        match self.phase {
            EvalStmtPhase::PreOperands => {
                self.perform_borrow_initial_pre_operand_actions()?;
                self.collapse_owned_places()?;
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
        match object {
            AnalysisObject::Statement(statement) => {
                self.visit_statement_fallable(statement, self.location)?
            }
            AnalysisObject::Terminator(terminator) => {
                self.visit_terminator_fallable(terminator, self.location)?
            }
        }
        Ok(self.actions)
    }

    fn update_latest_for_unblocked_places(
        &mut self,
        edge: &impl BorrowPcgEdgeLike<'tcx>,
        context: &str,
    ) -> Result<(), PcgError> {
        for place in edge.blocked_places(self.ctxt) {
            if let Some(place) = place.as_current_place()
                && self.pcg.capabilities.get(place) != Some(CapabilityKind::Read)
                && place.has_location_dependent_value(self.ctxt)
            {
                self.record_and_apply_action(
                    BorrowPcgAction::set_latest(
                        place,
                        SnapshotLocation::After(self.location),
                        context,
                    )
                    .into(),
                )?;
            }
        }
        Ok(())
    }

    fn update_unblocked_node_capabilities_and_remove_placeholder_projections(
        &mut self,
        edge: &impl BorrowPcgEdgeLike<'tcx>,
    ) -> Result<(), PcgError> {
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

                if blocked_cap.is_none() || matches!(blocked_cap, Some(CapabilityKind::ShallowExclusive))
                {
                    self.record_and_apply_action(PcgAction::restore_capability(
                        place,
                        restore_cap,
                        "restore_capabilities_for_removed_edge",
                        self.ctxt,
                    ))?;
                }
                for rp in place.region_projections(self.ctxt) {
                    self.record_and_apply_action(
                            BorrowPcgAction::remove_region_projection_label(
                                rp.with_placeholder_label(self.ctxt).into(),
                                format!(
                                    "Place {} unblocked: remove placeholder label of rps of newly unblocked nodes",
                                    place.to_short_string(self.ctxt)
                                ),
                            )
                            .into(),
                        )?;
                }
            }
        }
        Ok(())
    }

    /// As an optimzization, for expansions of the form {y, y|'y at l} -> *y,
    /// if *y doesn't contain any borrows, we currently don't introduce placeholder
    /// projections for y|'y: the set of borrows is guaranteed not to change as long as *y
    /// is in the graph.
    ///
    /// Accordingly, when we want to remove *y in such cases, we just remove the
    /// label rather than use the normal logic (of renaming the placeholder
    /// projection to the current one).
    fn unlabel_blocked_region_projections(
        &mut self,
        expansion: &BorrowPcgExpansion<'tcx>,
    ) -> Result<(), PcgError> {
        if let Some(node) = expansion.deref_blocked_region_projection(self.ctxt) {
            if let Some(PCGNode::RegionProjection(rp)) = node.try_to_local_node(self.ctxt) {
                self.record_and_apply_action(
                    BorrowPcgAction::remove_region_projection_label(
                        rp,
                        "unlabel blocked_region_projections",
                    )
                    .into(),
                )?;
            }
        }
        Ok(())
    }

    fn redirect_rp_expansion_to_base(
        &mut self,
        base: LocalRegionProjection<'tcx>,
        expansion: &[LocalRegionProjection<'tcx>],
    ) -> Result<(), PcgError> {
        for (idx, node) in expansion.iter().enumerate() {
            if let Some(place) = node.base.as_current_place() {
                let labeller = SetLabel(SnapshotLocation::BeforeCollapse(self.location));
                self.pcg.borrow.graph.make_place_old(
                    (*place).into(),
                    MakePlaceOldReason::Collapse,
                    &labeller,
                    self.ctxt,
                );
                let mut node = node.clone();
                node.label_place(
                    &LabelPlacePredicate::Exact((*place).into()),
                    &labeller,
                    self.ctxt,
                );
                let edge = BorrowPcgEdge::new(
                    BorrowFlowEdge::new(
                        node.into(),
                        base,
                        BorrowFlowEdgeKind::Aggregate {
                            field_idx: idx,
                            target_rp_index: 0,
                        },
                        self.ctxt,
                    )
                    .into(),
                    self.pcg.borrow.path_conditions.clone(),
                );
                self.record_and_apply_action(
                    BorrowPcgAction::add_edge(edge, "redirect blocked", false).into(),
                )?;
            }
        }
        Ok(())
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

    #[tracing::instrument(skip(self, edge))]
    pub(crate) fn remove_edge_and_perform_associated_state_updates(
        &mut self,
        edge: impl BorrowPcgEdgeLike<'tcx>,
        during_cleanup: bool,
        context: &str,
    ) -> Result<(), PcgError> {
        self.update_latest_for_unblocked_places(&edge, context)?;

        self.record_and_apply_action(
            BorrowPcgAction::remove_edge(edge.clone().to_owned_edge(), context).into(),
        )?;

        self.update_unblocked_node_capabilities_and_remove_placeholder_projections(&edge)?;

        match edge.kind() {
            BorrowPcgEdgeKind::BorrowPcgExpansion(expansion) => {
                // if let Some(lifetime_expansion) = expansion.try_to_lifetime_expansion()
                //     && lifetime_expansion.base.place().is_owned(self.ctxt)
                // {
                //     self.redirect_blocked_nodes_to_base(
                //         lifetime_expansion.base,
                //         lifetime_expansion.expansion(),
                //     )?;
                // }
                if let Some(place) = expansion.deref_blocked_place(self.ctxt)
                    && !place.regions(self.ctxt).iter().contains(
                        &expansion
                            .deref_blocked_region_projection(self.ctxt)
                            .unwrap()
                            .region(self.ctxt),
                    )
                {
                    self.unlabel_blocked_region_projections(expansion)?;
                }
                for exp_node in expansion.expansion() {
                    if let PCGNode::Place(place) = exp_node {
                        for rp in place.region_projections(self.ctxt) {
                            tracing::debug!(
                                "labeling region projection: {}",
                                rp.to_short_string(self.ctxt)
                            );
                            let snapshot_location = if during_cleanup {
                                SnapshotLocation::Prepare(self.location)
                            } else {
                                SnapshotLocation::before(self.location)
                            };
                            self.record_and_apply_action(
                                BorrowPcgAction::label_region_projection(
                                    rp,
                                    Some(RegionProjectionLabel::Location(snapshot_location)),
                                    format!(
                                        "{}: {}",
                                        context, "Label region projections of expansion"
                                    ),
                                )
                                .into(),
                            )?;
                        }
                    }
                }
            }
            BorrowPcgEdgeKind::Borrow(borrow) => {
                if self.ctxt.bc.is_dead(
                    borrow
                        .assigned_region_projection(self.ctxt)
                        .to_pcg_node(self.ctxt),
                    self.location,
                ) && let MaybeOldPlace::Current { place } = borrow.assigned_ref()
                    && let Some(existing_cap) = self.pcg.capabilities.get(place)
                {
                    self.record_and_apply_action(
                        BorrowPcgAction::weaken(
                            place,
                            existing_cap,
                            Some(CapabilityKind::Write),
                            "remove borrow edge",
                            self.ctxt,
                        )
                        .into(),
                    )?;
                }
            }
            _ => {}
        }
        Ok(())
    }

    #[tracing::instrument(skip(self, action))]
    fn record_and_apply_action(&mut self, action: PcgAction<'tcx>) -> Result<bool, PcgError> {
        tracing::debug!("Applying Action: {}", action.debug_line(self.ctxt));
        let result = match &action {
            PcgAction::Borrow(action) => self.pcg.borrow.apply_action(
                action.clone(),
                &mut self.pcg.capabilities,
                self.ctxt,
            )?,
            PcgAction::Owned(owned_action) => match owned_action.kind {
                RepackOp::RegainLoanedCapability(place, capability_kind) => self
                    .pcg
                    .capabilities
                    .insert((*place).into(), capability_kind, self.ctxt),
                RepackOp::Expand(expand) => {
                    self.pcg.owned.perform_expand_action(
                        expand,
                        &mut self.pcg.capabilities,
                        self.ctxt,
                    )?;
                    true
                }
                RepackOp::DerefShallowInit(from, to) => {
                    let target_places = from.expand_one_level(to, self.ctxt)?.expansion();
                    let capability_projections =
                        self.pcg.owned.locals_mut()[from.local].get_allocated_mut();
                    capability_projections.insert_expansion(
                        from,
                        PlaceExpansion::from_places(target_places.clone(), self.ctxt),
                    );
                    for target_place in target_places {
                        self.pcg
                            .capabilities
                            .insert(target_place, CapabilityKind::Read, self.ctxt);
                    }
                    true
                }
                RepackOp::Collapse(collapse) => {
                    let capability_projections =
                        self.pcg.owned.locals_mut()[collapse.local()].get_allocated_mut();
                    let expansion_places = collapse.expansion_places(self.ctxt);
                    let retained_cap =
                        expansion_places
                            .iter()
                            .fold(CapabilityKind::Exclusive, |acc, place| {
                                match self.pcg.capabilities.remove(*place, self.ctxt) {
                                    Some(cap) => acc.minimum(cap).unwrap_or(CapabilityKind::Write),
                                    None => acc,
                                }
                            });
                    self.pcg
                        .capabilities
                        .insert(collapse.to, retained_cap, self.ctxt);
                    capability_projections.expansions.remove(&collapse.to);
                    true
                }
                _ => unreachable!(),
            },
        };
        // self.pcg.borrow.graph.render_debug_graph(
        //     self.ctxt,
        //     &format!("after {}", action.debug_line(self.ctxt)),
        // );
        generate_dot_graph(
            self.location.block,
            self.location.statement_index,
            ToGraph::Action(self.phase, self.actions.len()),
            self.pcg,
            &self.debug_data,
            self.ctxt,
        );
        self.actions.push(action);
        Ok(result)
    }

    fn activate_twophase_borrow_created_at(
        &mut self,
        created_location: Location,
    ) -> Result<(), PcgError> {
        let borrow = match self.pcg.borrow.graph().borrow_created_at(created_location) {
            Some(borrow) => borrow,
            None => return Ok(()),
        };
        tracing::info!(
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
            self.remove_read_permission_upwards(blocked_place)?;
        }
        Ok(())
    }

    #[tracing::instrument(skip(self))]
    fn perform_borrow_initial_pre_operand_actions(&mut self) -> Result<(), PcgError> {
        self.pack_old_and_dead_borrow_leaves()?;
        for created_location in self.ctxt.bc.twophase_borrow_activations(self.location) {
            self.activate_twophase_borrow_created_at(created_location)?;
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
        let target_places = expand.target_places(ctxt);
        let capability_projections = self.locals_mut()[expand.local()].get_allocated_mut();
        capability_projections.insert_expansion(
            expand.from,
            PlaceExpansion::from_places(target_places.clone(), ctxt),
        );
        let source_cap = if expand.capability.is_read() {
            expand.capability
        } else {
            capabilities.get(expand.from).unwrap_or_else(|| {
                pcg_validity_assert!(false, "no cap for {}", expand.from.to_short_string(ctxt));
                panic!("no cap for {}", expand.from.to_short_string(ctxt));
                // For debugging, assume exclusive, we can visualize the graph to see what's going on
                // CapabilityKind::Exclusive
            })
        };
        for target_place in target_places {
            capabilities.insert(target_place, source_cap, ctxt);
        }
        if expand.capability.is_read() {
            capabilities.insert(expand.from, CapabilityKind::Read, ctxt);
        } else {
            capabilities.remove(expand.from, ctxt);
        }
        Ok(())
    }
}
