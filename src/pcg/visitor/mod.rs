use crate::action::{BorrowPcgAction, PcgAction};
use crate::borrow_pcg::action::MakePlaceOldReason;
use crate::borrow_pcg::borrow_pcg_edge::{BorrowPcgEdge, BorrowPcgEdgeLike};
use crate::borrow_pcg::borrow_pcg_expansion::{BorrowPcgExpansion, PlaceExpansion};
use crate::borrow_pcg::edge::kind::BorrowPcgEdgeKind;
use crate::borrow_pcg::edge::outlives::{BorrowFlowEdge, BorrowFlowEdgeKind};
use crate::borrow_pcg::region_projection::{PcgRegion, RegionProjection, RegionProjectionLabel};
use crate::free_pcs::{CapabilityKind, RepackOp};
use crate::pcg::dot_graphs::{generate_dot_graph, ToGraph};
use crate::pcg::triple::TripleWalker;
use crate::pcg::PcgDebugData;
use crate::rustc_interface::middle::mir::{self, Location, Operand, Rvalue, Statement, Terminator};
use crate::utils::data_structures::HashSet;
use crate::utils::display::DisplayWithCompilerCtxt;

use crate::action::PcgActions;
use crate::utils::maybe_old::MaybeOldPlace;
use crate::utils::visitor::FallableVisitor;
use crate::utils::{self, CompilerCtxt, HasPlace, Place, SnapshotLocation};

use super::{
    AnalysisObject, EvalStmtPhase, PCGNode, PCGNodeLike, PCGUnsupportedError, Pcg, PcgError,
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
        _location: Location,
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
        self.perform_statement_actions(statement, location)?;
        self.pcg.assert_validity_at_location(self.ctxt, location);
        Ok(())
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
                BorrowPcgAction::make_place_old(place, MakePlaceOldReason::MoveOut).into(),
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
            let destination: utils::Place<'tcx> = (*destination).into();
            self.record_and_apply_action(
                BorrowPcgAction::set_latest(destination, location, "Destination of Function Call")
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
    ) -> Result<PcgActions<'tcx>, PcgError> {
        match self.phase {
            EvalStmtPhase::PreOperands => {
                self.perform_borrow_initial_pre_operand_actions()?;
                self.collapse_owned_places()?;
                for triple in self.tw.operand_triples.iter() {
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

    fn update_latest_for_blocked_places(
        &mut self,
        edge: &impl BorrowPcgEdgeLike<'tcx>,
        location: Location,
        context: &str,
    ) -> Result<(), PcgError> {
        for place in edge.blocked_places(self.ctxt) {
            if let Some(place) = place.as_current_place()
                && self.pcg.capabilities.get(place.into()) != Some(CapabilityKind::Read)
                && place.has_location_dependent_value(self.ctxt)
            {
                self.record_and_apply_action(
                    BorrowPcgAction::set_latest(place, location, context).into(),
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

                if blocked_cap.is_none()
                    || (blocked_cap.unwrap().is_read() && place.place().projection.is_empty())
                {
                    self.record_and_apply_action(PcgAction::restore_capability(
                        place,
                        restore_cap,
                        "restore_capabilities_for_removed_edge",
                        self.ctxt,
                    ))?;
                    for rp in place.region_projections(self.ctxt) {
                        let placeholder_rp =
                            rp.with_label(Some(RegionProjectionLabel::Placeholder), self.ctxt);
                        self.record_and_apply_action(
                            BorrowPcgAction::label_region_projection(
                                placeholder_rp.into(),
                                None,
                                "update_unblocked_node_capabilities_and_remove_placeholder_projections",
                            )
                            .into(),
                        )?;
                    }
                }
            }
        }
        Ok(())
    }

    fn unlabel_blocked_region_projections(
        &mut self,
        expansion: &BorrowPcgExpansion<'tcx>,
    ) -> Result<(), PcgError> {
        if let Some(node) = expansion.deref_blocked_region_projection(self.ctxt) {
            if let Some(PCGNode::RegionProjection(rp)) = node.try_to_local_node(self.ctxt) {
                self.record_and_apply_action(
                    BorrowPcgAction::label_region_projection(
                        rp.into(),
                        None,
                        "unlabel_blocked_region_projections",
                    )
                    .into(),
                )?;
            }
        }
        Ok(())
    }

    fn redirect_blocked_nodes_to_base(
        &mut self,
        expansion: &BorrowPcgExpansion<'tcx>,
    ) -> Result<(), PcgError> {
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
                    self.record_and_apply_action(
                        BorrowPcgAction::redirect_edge(
                            to_redirect,
                            *node,
                            expansion.base,
                            "redirect_blocked_nodes_to_base",
                        )
                        .into(),
                    )?;
                }
            }
        }
        Ok(())
    }

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
                    if !seen.contains(&(node.into())) {
                        stack.push(node.into());
                    }
                }
            }
        }
        return false;
    }

    fn reconnect_current_rps(&mut self, place: Place<'tcx>, context: &str) -> Result<(), PcgError> {
        let frozen_graph = self.pcg.borrow.graph().frozen_graph();
        let leaf_nodes = frozen_graph
            .leaf_nodes(self.ctxt)
            .filter_map(|node| {
                if let PCGNode::RegionProjection(rp) = node {
                    Some(rp)
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();
        let label = RegionProjectionLabel::Location(SnapshotLocation::before(self.location));
        let mut to_add_actions = vec![];
        let mut leaf_nodes_to_label = HashSet::default();
        for place_rp in place.region_projections(self.ctxt) {
            if frozen_graph.contains(place_rp.into(), self.ctxt) {
                continue;
            }
            let ctxt = self.ctxt;
            for leaf_node in leaf_nodes.iter().copied() {
                if !self
                    .ctxt
                    .bc
                    .outlives(leaf_node.region(self.ctxt), place_rp.region(self.ctxt))
                {
                    continue;
                }
                if self.any_reachable_reverse(leaf_node.into(), |node| {
                    if let PCGNode::RegionProjection(rp) = node {
                        rp.base == place_rp.base.into() && rp.region(ctxt) == place_rp.region(ctxt)
                    } else {
                        false
                    }
                }) {
                    let mut edge_leaf_node = leaf_node
                        .to_pcg_node(self.ctxt)
                        .try_into_region_projection()
                        .unwrap();
                    if !edge_leaf_node.is_placeholder() {
                        leaf_nodes_to_label.insert(leaf_node.into());
                        edge_leaf_node = edge_leaf_node.with_label(Some(label), self.ctxt);
                    }
                    to_add_actions.push(BorrowPcgAction::add_edge(
                        BorrowPcgEdge::new(
                            BorrowFlowEdge::new(
                                edge_leaf_node.into(),
                                place_rp.into(),
                                BorrowFlowEdgeKind::UpdateNestedRefs,
                                self.ctxt,
                            )
                            .into(),
                            self.pcg.borrow.path_conditions.clone(),
                        ),
                        format!(
                            "{}: Reconnect Region Projections: {} is an ancestor of leaf node {}",
                            context,
                            place_rp.to_short_string(self.ctxt),
                            leaf_node.to_short_string(self.ctxt),
                        ),
                        false,
                    ));
                }
            }
        }
        for leaf_node in leaf_nodes_to_label {
            self.record_and_apply_action(
                BorrowPcgAction::label_region_projection(
                    leaf_node,
                    Some(label),
                    format!(
                        "{}: Reconnect Region Projections for place {}",
                        context,
                        place.to_short_string(self.ctxt)
                    ),
                )
                .into(),
            )?;
        }
        for action in to_add_actions {
            self.record_and_apply_action(action.into())?;
        }
        Ok(())
    }

    #[tracing::instrument(skip(self, edge, location))]
    pub(crate) fn remove_edge_and_perform_associated_state_updates(
        &mut self,
        edge: impl BorrowPcgEdgeLike<'tcx>,
        location: Location,
        context: &str,
    ) -> Result<(), PcgError> {
        self.update_latest_for_blocked_places(&edge, location, context)?;

        self.record_and_apply_action(
            BorrowPcgAction::remove_edge(edge.clone().to_owned_edge(), context).into(),
        )?;

        self.update_unblocked_node_capabilities_and_remove_placeholder_projections(&edge)?;

        if let BorrowPcgEdgeKind::BorrowPcgExpansion(expansion) = edge.kind() {
            if expansion.is_mutable_deref(self.ctxt) {
                self.unlabel_blocked_region_projections(expansion)?;
            }
            self.redirect_blocked_nodes_to_base(expansion)?;
        }
        if matches!(
            edge.kind(),
            BorrowPcgEdgeKind::BorrowPcgExpansion(_) | BorrowPcgEdgeKind::Borrow(_)
        ) {
            for blocked_node in edge.blocked_nodes(self.ctxt) {
                if let Some(local_node) = blocked_node.try_to_local_node(self.ctxt) {
                    match local_node {
                        PCGNode::RegionProjection(rp) => {
                            self.reconnect_current_rps(rp.base.place(), context)?;
                        }
                        PCGNode::Place(place) => {
                            self.reconnect_current_rps(place.place(), context)?;
                        }
                    }
                }
            }
        }
        Ok(())
    }

    #[tracing::instrument(skip(self, action))]
    fn record_and_apply_action(&mut self, action: PcgAction<'tcx>) -> Result<bool, PcgError> {
        let result =
            match &action {
                PcgAction::Borrow(action) => self.pcg.borrow.apply_action(
                    action.clone(),
                    &mut self.pcg.capabilities,
                    self.ctxt,
                )?,
                PcgAction::Owned(owned_action) => match owned_action.kind {
                    RepackOp::RegainLoanedCapability(place, capability_kind) => self
                        .pcg
                        .capabilities
                        .insert((*place).into(), capability_kind),
                    RepackOp::Expand(from, to, capability) => {
                        let target_places = from.expand_one_level(to, self.ctxt)?.expansion();
                        let capability_projections =
                            self.pcg.owned.locals_mut()[from.local].get_allocated_mut();
                        capability_projections.insert_expansion(
                            from,
                            PlaceExpansion::from_places(target_places.clone(), self.ctxt),
                        );
                        let source_cap = if capability.is_read() {
                            capability
                        } else {
                            self.pcg.capabilities.get((*from).into()).unwrap()
                        };
                        tracing::info!("source_cap for {:?}: {:?}", owned_action, source_cap);
                        for target_place in target_places {
                            self.pcg
                                .capabilities
                                .insert(target_place.into(), source_cap);
                        }
                        // if source_cap > *capability {
                        //     self.pcg.capabilities.insert((*to).into(), *capability);
                        // }
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
                                .insert(target_place.into(), CapabilityKind::Read);
                        }
                        true
                    }
                    RepackOp::Collapse(base_place, proj_place, _) => {
                        let capability_projections =
                            self.pcg.owned.locals_mut()[base_place.local].get_allocated_mut();
                        let expansion_places = base_place
                            .expand_one_level(proj_place, self.ctxt)?
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
                        capability_projections.expansions.remove(&base_place);
                        true
                    }
                    _ => unreachable!(),
                },
            };
        self.pcg.borrow.graph.render_debug_graph(
            self.ctxt,
            &format!("after {}", action.debug_line(self.ctxt)),
        );
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

    #[tracing::instrument(skip(self))]
    fn perform_borrow_initial_pre_operand_actions(&mut self) -> Result<(), PcgError> {
        self.pack_old_and_dead_borrow_leaves(self.location)?;
        for created_location in self.ctxt.bc.twophase_borrow_activations(self.location) {
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
                let upgrade_action = BorrowPcgAction::restore_capability(
                    borrow.deref_place(self.ctxt).place().into(),
                    CapabilityKind::Exclusive,
                    "perform_borrow_initial_pre_operand_actions",
                );
                self.record_and_apply_action(upgrade_action.into())?;
            }
            if !blocked_place.is_owned(self.ctxt) {
                self.remove_read_permission_upwards(blocked_place)?;
            }
            for place in blocked_place.iter_places(self.ctxt) {
                for rp in place.region_projections(self.ctxt).into_iter() {
                    if rp.can_be_labelled(self.ctxt) {
                        self.record_and_apply_action(
                            BorrowPcgAction::label_region_projection(
                                rp.into(),
                                None,
                                "perform_borrow_initial_pre_operand_actions",
                            )
                            .into(),
                        )?;
                    }
                }
            }
        }
        Ok(())
    }
}
