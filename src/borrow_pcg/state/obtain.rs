use crate::borrow_pcg::action::executed_actions::ExecutedActions;
use crate::borrow_pcg::action::BorrowPCGAction;
use crate::borrow_pcg::borrow_pcg_edge::BorrowPCGEdge;
use crate::borrow_pcg::borrow_pcg_expansion::{BorrowExpansion, BorrowPCGExpansion};
use crate::borrow_pcg::graph::borrows_imgcat_debug;
use crate::borrow_pcg::path_condition::PathConditions;
use crate::borrow_pcg::region_projection::RegionProjection;
use crate::borrow_pcg::region_projection_member::{
    RegionProjectionMember, RegionProjectionMemberKind,
};
use crate::borrow_pcg::state::BorrowsState;
use crate::borrow_pcg::unblock_graph::UnblockGraph;
use crate::combined_pcs::{PCGError, PCGNodeLike};
use crate::free_pcs::CapabilityKind;
use crate::rustc_interface::middle::mir::{BorrowKind, Location, MutBorrowKind};
use crate::rustc_interface::middle::ty::{self, Mutability};
use crate::utils::maybe_old::MaybeOldPlace;
use crate::utils::{Place, PlaceRepacker};
use crate::visualization::dot_graph::DotGraph;
use crate::visualization::generate_borrows_dot_graph;
use smallvec::smallvec;

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
                    MutBorrowKind::TwoPhaseBorrow => CapabilityKind::LentShared,
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
    #[must_use]
    pub(crate) fn obtain(
        &mut self,
        repacker: PlaceRepacker<'_, 'tcx>,
        place: Place<'tcx>,
        location: Location,
        obtain_reason: ObtainReason,
    ) -> Result<ExecutedActions<'tcx>, PCGError> {
        let mut actions = ExecutedActions::new();
        if obtain_reason.min_post_obtain_capability() != CapabilityKind::Read {
            actions.extend(self.contract_to(place, location, repacker)?);
        }

        if !self.contains(place, repacker) {
            let extra_acts = self.expand_to(place.into(), repacker, location)?;
            actions.extend(extra_acts);
        }

        Ok(actions)
    }

    /// Contracts the PCG to the given place by converting borrows to region projection members
    /// and performing unblock operations.
    #[must_use]
    pub(crate) fn contract_to(
        &mut self,
        place: Place<'tcx>,
        location: Location,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Result<ExecutedActions<'tcx>, PCGError> {
        let mut actions = ExecutedActions::new();

        {
            let encapsulated_borrow_edges = self
                .graph()
                .borrows()
                .filter(|borrow| match borrow.value.assigned_ref {
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
                ));
                for ra in place.region_projections(repacker) {
                    self.record_and_apply_action(
                        BorrowPCGAction::add_region_projection_member(
                            RegionProjectionMember::new(
                                smallvec![borrow.value.blocked_place.into()],
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
                    ug.unblock_node(root_node.into(), self, repacker);
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
                    smallvec![base_rp.to_pcg_node(repacker)],
                    smallvec![target.into()],
                    RegionProjectionMemberKind::DerefRegionProjection,
                );

                self.record_and_apply_action(
                    BorrowPCGAction::add_region_projection_member(
                        region_projection_member,
                        PathConditions::new(location.block),
                        "Expand",
                    ),
                    &mut actions,
                    repacker,
                );
            }

            // We don't introduce an expansion if the place is owned, because
            // that is handled by the owned PCG.
            if !target.is_owned(repacker) {
                let expansion = BorrowPCGExpansion::new(
                    base.into(),
                    BorrowExpansion::from_places(expansion.clone(), repacker),
                    repacker,
                );

                let action = BorrowPCGAction::insert_borrow_pcg_expansion(
                    expansion,
                    location,
                    "Ensure Deref Expansion (Place)",
                );
                self.record_and_apply_action(action, &mut actions, repacker);
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

        Ok(actions)
    }
}
