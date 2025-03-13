use std::collections::BTreeSet;

use crate::borrow_pcg::action::executed_actions::ExecutedActions;
use crate::borrow_pcg::action::BorrowPCGAction;
use crate::borrow_pcg::borrow_pcg_edge::{BorrowPCGEdge, LocalNode};
use crate::borrow_pcg::borrow_pcg_expansion::{BorrowPCGExpansion, PlaceExpansion};
use crate::borrow_pcg::edge::kind::BorrowPCGEdgeKind;
use crate::borrow_pcg::edge::region_projection_member::{
    RegionProjectionMember, RpMemberDirection,
};
use crate::borrow_pcg::graph::borrows_imgcat_debug;
use crate::borrow_pcg::path_condition::PathConditions;
use crate::borrow_pcg::region_projection::RegionProjection;
use crate::borrow_pcg::state::BorrowsState;
use crate::borrow_pcg::unblock_graph::UnblockGraph;
use crate::combined_pcs::{PCGNodeLike, PcgError};
use crate::free_pcs::CapabilityKind;
use crate::pcg_validity_assert;
use crate::rustc_interface::middle::mir::{BorrowKind, Location, MutBorrowKind};
use crate::rustc_interface::middle::ty::Mutability;
use crate::utils::maybe_old::MaybeOldPlace;
use crate::utils::{HasPlace, Place, PlaceRepacker};
use crate::visualization::dot_graph::DotGraph;
use crate::visualization::generate_borrows_dot_graph;

impl ObtainReason {
    /// After calling `obtain` for a place, the minimum capability that we
    /// expect the place to have.
    pub(crate) fn min_post_obtain_capability(&self) -> CapabilityKind {
        match self {
            ObtainReason::MoveOperand => CapabilityKind::Exclusive,
            ObtainReason::CopyOperand => CapabilityKind::Read,
            ObtainReason::FakeRead => CapabilityKind::Read,
            ObtainReason::AssignTarget => CapabilityKind::Write,
            ObtainReason::CreateReference(borrow_kind) => match borrow_kind {
                BorrowKind::Shared => CapabilityKind::Read,
                BorrowKind::Fake(_) => unreachable!(),
                BorrowKind::Mut { kind } => match kind {
                    MutBorrowKind::Default => CapabilityKind::Exclusive,
                    MutBorrowKind::TwoPhaseBorrow => CapabilityKind::Read,
                    MutBorrowKind::ClosureCapture => CapabilityKind::Exclusive,
                },
            },
            ObtainReason::CreatePtr(mutability) => {
                if mutability.is_mut() {
                    CapabilityKind::Exclusive
                } else {
                    CapabilityKind::Read
                }
            }
            ObtainReason::RValueSimpleRead => CapabilityKind::Read,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum ObtainReason {
    MoveOperand,
    CopyOperand,
    FakeRead,
    AssignTarget,
    CreateReference(BorrowKind),
    CreatePtr(Mutability),
    /// Just to read the place, but not refer to it
    RValueSimpleRead,
}

impl<'tcx> BorrowsState<'tcx> {
    /// Ensures that the place is expanded to the given place, with a certain
    /// capability.
    ///
    /// This also handles corresponding region projections of the place.
    #[tracing::instrument(skip(self, repacker, location, obtain_reason))]
    pub(crate) fn obtain(
        &mut self,
        repacker: PlaceRepacker<'_, 'tcx>,
        place: Place<'tcx>,
        location: Location,
        obtain_reason: ObtainReason,
    ) -> Result<ExecutedActions<'tcx>, PcgError> {
        let mut actions = ExecutedActions::new();
        if obtain_reason.min_post_obtain_capability() != CapabilityKind::Read {
            actions.extend(self.contract_to(place, location, repacker)?);
        }

        if !self.contains(place, repacker) {
            let extra_acts = self.expand_to(place, repacker, obtain_reason, location)?;
            actions.extend(extra_acts);
        }
        if !place.is_owned(repacker) {
            pcg_validity_assert!(
                self.get_capability(place.into()).is_some(),
                "Place {:?} does not have a capability after obtain {:?}",
                place,
                obtain_reason
            );
            pcg_validity_assert!(
                self.get_capability(place.into()).unwrap()
                    >= obtain_reason.min_post_obtain_capability(),
                "{:?} Capability {:?} for {:?} is not greater than {:?}",
                location,
                self.get_capability(place.into()).unwrap(),
                place,
                obtain_reason.min_post_obtain_capability()
            );
        }
        Ok(actions)
    }

    /// Contracts the PCG to the given place by converting borrows to region projection members
    /// and performing unblock operations.
    pub(crate) fn contract_to(
        &mut self,
        place: Place<'tcx>,
        location: Location,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Result<ExecutedActions<'tcx>, PcgError> {
        let mut actions = ExecutedActions::new();

        {
            let encapsulated_borrow_edges = self
                .graph()
                .borrows()
                .filter(|borrow| match borrow.value.assigned_ref() {
                    MaybeOldPlace::Current {
                        place: assigned_place,
                    } => place.is_strict_prefix(assigned_place),
                    _ => false,
                })
                .collect::<Vec<_>>();

            // If we are going to contract a place, borrows may need to be converted
            // to region projection member edges. For example, if the type of `x.t` is
            // `&'a mut T` and there is a borrow `x.t = &mut y`, and we need to contract to `x`, then we need
            // to replace the borrow edge with an edge `{y} -> {x↓'a}`.
            for borrow in encapsulated_borrow_edges {
                let to_remove: BorrowPCGEdge<'tcx> = borrow.clone().into();
                actions.extend(self.remove_edge_and_set_latest(
                    to_remove,
                    location,
                    repacker,
                    &format!("Contract To {:?}", place),
                )?);
                for ra in place.region_projections(repacker) {
                    self.record_and_apply_action(
                        BorrowPCGAction::add_edge(
                            BorrowPCGEdge::new(
                                RegionProjectionMember::new(
                                    ra.set_base(ra.base().into(), repacker),
                                    borrow.value.blocked_place(),
                                    RpMemberDirection::PlaceOutlivesRegion,
                                )
                                .into(),
                                PathConditions::new(location.block),
                            ),
                            true,
                        ),
                        &mut actions,
                        repacker,
                    )?;
                }
            }
        }

        let mut ug = UnblockGraph::new();
        ug.unblock_node(place.to_pcg_node(repacker), self, repacker);
        for rp in place.region_projections(repacker) {
            ug.unblock_node(rp.to_pcg_node(repacker), self, repacker);
        }

        // The place itself could be in the owned PCG, but we want to unblock
        // the borrowed parts. For example if the place is a struct S, with
        // owned fields S.f and S.g, we will want to unblock S.f and S.g.
        for root_node in self.roots(repacker) {
            if let Some(root_node_place) = root_node.as_current_place() {
                if place.is_prefix(root_node_place) {
                    ug.unblock_node(root_node, self, repacker);
                }
            }
        }
        let unblock_actions = ug.actions(repacker).unwrap_or_else(|e| {
            if borrows_imgcat_debug() {
                let dot_graph = generate_borrows_dot_graph(repacker, self.graph()).unwrap();
                DotGraph::render_with_imgcat(&dot_graph, "Borrows graph for unblock actions")
                    .unwrap_or_else(|e| {
                        eprintln!("Error rendering borrows graph: {}", e);
                    });
            }
            panic!("Error when contracting to {:?}: {:?}", place, e);
        });
        for action in unblock_actions {
            actions.extend(self.remove_edge_and_set_latest(
                action.edge,
                location,
                repacker,
                &format!("Contract To {:?}", place),
            )?);
        }

        // It's possible that `place` is not in the PCG, `expand_root` is the leaf
        // node from which place will be expanded to.

        let mut expand_root = place;
        while self.get_capability(expand_root.into()).is_none() {
            if expand_root.is_owned(repacker) {
                return Ok(actions);
            }
            expand_root = expand_root.parent_place().unwrap();
        }

        // The expand_root may have capability read only. If we need an exclusive permission,
        // then we need to change all Read permissions from `expand_root`'s parents to be None
        // instead to ensure they are no longer accessible.

        if !expand_root.is_owned(repacker)
            && self.get_capability(expand_root.into()) == Some(CapabilityKind::Read)
        {
            tracing::info!("Capability {:?} for {:?} is read", expand_root, location);
            self.record_and_apply_action(
                BorrowPCGAction::restore_capability(expand_root.into(), CapabilityKind::Exclusive),
                &mut actions,
                repacker,
            )?;
            let mut current = expand_root.parent_place().unwrap();
            while !current.is_owned(repacker)
                && self.get_capability(current.into()) == Some(CapabilityKind::Read)
            {
                self.record_and_apply_action(
                    BorrowPCGAction::weaken(current, CapabilityKind::Read, None),
                    &mut actions,
                    repacker,
                )?;
                let parent = match current.parent_place() {
                    Some(parent) => parent,
                    None => break,
                };
                current = parent;
            }
        }

        Ok(actions)
    }

    /// Inserts edges to ensure that the borrow PCG is expanded to at least
    /// `to_place`. We assume that any unblock operations have already been
    /// performed.
    fn expand_to(
        &mut self,
        to_place: Place<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
        obtain_reason: ObtainReason,
        location: Location,
    ) -> Result<ExecutedActions<'tcx>, PcgError> {
        let for_exclusive = obtain_reason.min_post_obtain_capability() != CapabilityKind::Read;
        let mut actions = ExecutedActions::new();

        for (base, _) in to_place.iter_projections(repacker) {
            let base: Place<'tcx> = base;
            let base = base.with_inherent_region(repacker);
            let expand_result = base.expand_one_level(to_place, repacker)?;
            let expansion = expand_result.expansion();
            let target = expand_result.target_place;

            // We don't introduce an expansion if the place is owned, because
            // that is handled by the owned PCG.
            if !target.is_owned(repacker) {
                let place_expansion = PlaceExpansion::from_places(expansion.clone(), repacker);
                let expansion: BorrowPCGExpansion<'tcx, LocalNode<'tcx>> = BorrowPCGExpansion::new(
                    base.into(),
                    place_expansion
                        .elems()
                        .into_iter()
                        .map(|p| base.project_deeper(p, repacker))
                        .collect::<Result<BTreeSet<_>, _>>()?
                        .into_iter()
                        .map(|p| p.into())
                        .collect(),
                );

                let action = BorrowPCGAction::add_edge(
                    BorrowPCGEdge::new(
                        BorrowPCGEdgeKind::BorrowPCGExpansion(expansion),
                        PathConditions::new(location.block),
                    ),
                    for_exclusive,
                );
                self.record_and_apply_action(action, &mut actions, repacker)?;
            }

            for rp in base.region_projections(repacker) {
                let dest_places = expansion
                    .iter()
                    .filter(|e| {
                        e.region_projections(repacker)
                            .into_iter()
                            .any(|child_rp| rp.region(repacker) == child_rp.region(repacker))
                    })
                    .copied()
                    .collect::<Vec<_>>();
                if !dest_places.is_empty() {
                    let rp: RegionProjection<'tcx, MaybeOldPlace<'tcx>> = rp.into();
                    let expansion = PlaceExpansion::from_places(dest_places, repacker);
                    let expansion_places: BTreeSet<LocalNode<'tcx>> = expansion
                        .elems()
                        .into_iter()
                        .map(|p| rp.project_deeper(p, repacker))
                        .collect::<Result<BTreeSet<_>, _>>()?
                        .into_iter()
                        .map(|p| p.into())
                        .collect();
                    self.record_and_apply_action(
                        BorrowPCGAction::add_edge(
                            BorrowPCGEdge::new(
                                BorrowPCGEdgeKind::BorrowPCGExpansion(BorrowPCGExpansion::new(
                                    rp.into(),
                                    expansion_places,
                                )),
                                PathConditions::new(location.block),
                            ),
                            for_exclusive,
                        ),
                        &mut actions,
                        repacker,
                    )?;
                }
            }
        }

        Ok(actions)
    }
}
