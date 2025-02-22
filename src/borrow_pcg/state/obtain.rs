use smallvec::smallvec;
use crate::borrow_pcg::action::BorrowPCGAction;
use crate::borrow_pcg::action::executed_actions::ExecutedActions;
use crate::borrow_pcg::borrow_pcg_edge::{BorrowPCGEdge, BorrowPCGEdgeLike, ToBorrowsEdge};
use crate::borrow_pcg::borrow_pcg_expansion::{BorrowExpansion, BorrowPCGExpansion};
use crate::borrow_pcg::edge::kind::BorrowPCGEdgeKind;
use crate::borrow_pcg::graph::borrows_imgcat_debug;
use crate::borrow_pcg::path_condition::PathConditions;
use crate::borrow_pcg::region_projection::RegionProjection;
use crate::borrow_pcg::region_projection_member::{RegionProjectionMember, RegionProjectionMemberKind};
use crate::borrow_pcg::state::BorrowsState;
use crate::borrow_pcg::unblock_graph::{UnblockGraph, UnblockType};
use crate::combined_pcs::{PCGError, PCGNodeLike};
use crate::rustc_interface::middle::mir::{BorrowKind, MutBorrowKind, Location};
use crate::rustc_interface::middle::ty::{Mutability, self};
use crate::free_pcs::CapabilityKind;
use crate::utils::{Place, PlaceRepacker};
use crate::utils::maybe_old::MaybeOldPlace;
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
                BorrowKind::Shared => CapabilityKind::LentShared,
                BorrowKind::Fake(_) => unreachable!(),
                BorrowKind::Mut { kind } => match kind {
                    MutBorrowKind::Default => CapabilityKind::Exclusive,
                    MutBorrowKind::TwoPhaseBorrow => CapabilityKind::LentShared,
                    MutBorrowKind::ClosureCapture => CapabilityKind::Exclusive,
                },
            },
            ObtainReason::CreatePtr(mutability) => {
                if mutability.is_mut() {
                    CapabilityKind::Exclusive
                } else {
                    CapabilityKind::LentShared
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
    #[must_use]
    pub(crate) fn obtain(
        &mut self,
        repacker: PlaceRepacker<'_, 'tcx>,
        place: Place<'tcx>,
        location: Location,
        expansion_reason: ObtainReason,
    ) -> Result<ExecutedActions<'tcx>, PCGError> {
        let mut actions = ExecutedActions::new();
        actions.extend(self.contract_to(repacker, place, location, expansion_reason.clone())?);

        if self.contains(place, repacker) {
            if self.get_capability(place.into()) == None {
                let expected_capability = expansion_reason.min_post_obtain_capability();
                self.record_and_apply_action(
                    BorrowPCGAction::restore_capability(place.into(), expected_capability),
                    &mut actions,
                    repacker,
                );
            }
        } else {
            let extra_acts = self.expand_to(place.into(), repacker, location)?;
            actions.extend(extra_acts);
        }

        Ok(actions)
    }

    /// Contracts the PCG to the given place by converting borrows to region projection members
    /// and performing unblock operations.
    #[must_use]
    fn contract_to(
        &mut self,
        repacker: PlaceRepacker<'_, 'tcx>,
        place: Place<'tcx>,
        location: Location,
        expansion_reason: ObtainReason,
    ) -> Result<ExecutedActions<'tcx>, PCGError> {
        let mut actions = ExecutedActions::new();

        let graph_edges = self
            .graph
            .edges()
            .map(|e| e.to_owned_edge())
            .collect::<Vec<_>>();

        // If we are going to contract a place, borrows may need to be converted
        // to region projection member edges. For example, if the type of `x.t` is
        // `&'a mut T` and there is a borrow `x.t = &mut y`, and we need to contract to `x`, then we need
        // to replace the borrow edge with an edge `{y} -> {x↓'a}`.
        for p in graph_edges {
            match p.kind() {
                BorrowPCGEdgeKind::Borrow(borrow) => match borrow.assigned_ref {
                    MaybeOldPlace::Current {
                        place: assigned_place,
                    } if place.is_prefix(assigned_place) && !place.is_ref(repacker) => {
                        for ra in place.region_projections(repacker) {
                            self.record_and_apply_action(
                                BorrowPCGAction::add_region_projection_member(
                                    RegionProjectionMember::new(
                                        smallvec![borrow.blocked_place.into()],
                                        smallvec![ra.into()],
                                        RegionProjectionMemberKind::ContractRef,
                                    ),
                                    PathConditions::new(location.block),
                                    "Contract To",
                                ),
                                &mut actions,
                                repacker,
                            );
                        }
                    }
                    _ => {}
                },
                _ => {}
            }
        }

        let unblock_type = match expansion_reason {
            ObtainReason::MoveOperand => UnblockType::ForRead,
            ObtainReason::CopyOperand => UnblockType::ForExclusive,
            ObtainReason::FakeRead => UnblockType::ForRead,
            ObtainReason::AssignTarget => UnblockType::ForExclusive,
            ObtainReason::CreateReference(borrow_kind) => match borrow_kind {
                BorrowKind::Shared => UnblockType::ForRead,
                BorrowKind::Fake(_) => unreachable!(),
                BorrowKind::Mut { kind } => match kind {
                    MutBorrowKind::Default => UnblockType::ForExclusive,
                    MutBorrowKind::TwoPhaseBorrow => UnblockType::ForRead,
                    MutBorrowKind::ClosureCapture => UnblockType::ForExclusive,
                },
            },
            ObtainReason::CreatePtr(mutability) => {
                if mutability == Mutability::Mut {
                    UnblockType::ForExclusive
                } else {
                    UnblockType::ForRead
                }
            }
            ObtainReason::RValueSimpleRead => UnblockType::ForRead,
        };

        let mut ug = UnblockGraph::new();
        ug.unblock_node(place.to_pcg_node(), self, repacker, unblock_type);
        for rp in place.region_projections(repacker) {
            ug.unblock_node(rp.to_pcg_node(), self, repacker, unblock_type);
        }

        // The place itself could be in the owned PCG, but we want to unblock
        // the borrowed parts. For example if the place is a struct S, with
        // owned fields S.f and S.g, we will want to unblock S.f and S.g.
        for root_node in self.roots(repacker) {
            if let Some(root_node_place) = root_node.as_current_place() {
                if place.is_prefix(root_node_place) {
                    ug.unblock_node(root_node.into(), self, repacker, unblock_type);
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
            panic!(
                "Error when contracting to {:?}: {:?}",
                place, e
            );
        });
        for action in unblock_actions {
            actions.extend(self.apply_unblock_action(
                action,
                repacker,
                location,
                &format!("Contract To {:?}", place),
            ));
        }

        Ok(actions)
    }

    /// Inserts edges to ensure that the borrow PCG is expanded to at least
    /// `to_place`. We assume that any unblock operations have already been
    /// performed.
    #[must_use]
    fn expand_to(
        &mut self,
        to_place: Place<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
        location: Location,
    ) -> Result<ExecutedActions<'tcx>, PCGError> {
        let mut actions = ExecutedActions::new();

        for (base, _) in to_place.iter_projections() {
            let base: Place<'tcx> = base.into();
            let base = base.with_inherent_region(repacker);
            let (target, mut expansion, kind) = base.expand_one_level(to_place, repacker)?;
            kind.insert_target_into_expansion(target, &mut expansion);

            if let ty::TyKind::Ref(region, _, _) = base.ty(repacker).ty.kind() {
                // This is a dereference, taking the the form t -> *t where t
                // has type &'a T. We insert a region projection member for t↓'a
                // -> *t if it doesn't already exist.

                // e.g t|'a
                let base_rp = RegionProjection::new((*region).into(), base, repacker).unwrap();

                let region_projection_member = RegionProjectionMember::new(
                    smallvec![base_rp.to_pcg_node()],
                    smallvec![target.into()],
                    RegionProjectionMemberKind::DerefRegionProjection,
                );

                let path_conditions = PathConditions::new(location.block);

                if !self.contains_edge(&BorrowPCGEdge::new(
                    region_projection_member.clone().into(),
                    path_conditions.clone(),
                )) {
                    self.record_and_apply_action(
                        BorrowPCGAction::add_region_projection_member(
                            region_projection_member,
                            path_conditions.clone(),
                            "Ensure Deref Expansion To At Least",
                        ),
                        &mut actions,
                        repacker,
                    );
                }
                // We also do this for all target region projections

                for target_rp in target.region_projections(repacker) {
                    let region_projection_member = RegionProjectionMember::new(
                        smallvec![base_rp.to_pcg_node()],
                        smallvec![target_rp.into()],
                        RegionProjectionMemberKind::DerefBorrowOutlives,
                    );

                    if !self.contains_edge(&BorrowPCGEdge::new(
                        region_projection_member.clone().into(),
                        path_conditions.clone(),
                    )) {
                        self.record_and_apply_action(
                            BorrowPCGAction::add_region_projection_member(
                                region_projection_member,
                                path_conditions.clone(),
                                "Ensure Deref Expansion To At Least",
                            ),
                            &mut actions,
                            repacker,
                        );
                    }
                }
            }

            if !target.is_owned(repacker) {
                let expansion = BorrowPCGExpansion::new(
                    base.into(),
                    BorrowExpansion::from_places(expansion.clone(), repacker),
                    repacker,
                );

                if !self.contains_edge(
                    &expansion
                        .clone()
                        .to_borrow_pcg_edge(PathConditions::AtBlock(location.block)),
                ) {
                    let action = BorrowPCGAction::insert_borrow_pcg_expansion(
                        expansion,
                        location,
                        "Ensure Deref Expansion (Place)",
                    );
                    self.record_and_apply_action(action, &mut actions, repacker);
                }
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
                if dest_places.len() > 0 {
                    let expansion = BorrowPCGExpansion::from_borrowed_base(
                        rp.into(),
                        BorrowExpansion::from_places(dest_places, repacker),
                        repacker,
                    );
                    let path_conditions = PathConditions::new(location.block);
                    if !self.contains_edge(&expansion.clone().to_borrow_pcg_edge(path_conditions)) {
                        self.record_and_apply_action(
                            BorrowPCGAction::insert_borrow_pcg_expansion(
                                expansion,
                                location,
                                "Ensure Deref Expansion (Region Projection)",
                            ),
                            &mut actions,
                            repacker,
                        );
                    }
                }
            }
        }

        Ok(actions)
    }

}
