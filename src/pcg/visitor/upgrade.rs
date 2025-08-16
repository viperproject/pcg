use itertools::Itertools;

use crate::{
    action::BorrowPcgAction,
    borrow_pcg::{
        borrow_pcg_edge::{BorrowPcgEdge, BorrowPcgEdgeLike},
        edge::{
            kind::BorrowPcgEdgeKind,
            outlives::{BorrowFlowEdge, BorrowFlowEdgeKind},
        },
        has_pcs_elem::LabelLifetimeProjectionPredicate,
        region_projection::LifetimeProjection,
    },
    error::PcgError,
    pcg::{
        CapabilityKind, PcgNode,
        obtain::{HasSnapshotLocation, PlaceObtainer},
        place_capabilities::{BlockType, PlaceCapabilitiesReader},
    },
    utils::{DataflowCtxt, Place, data_structures::HashSet, display::DisplayWithCompilerCtxt},
};

impl<'state, 'a: 'state, 'tcx: 'a, Ctxt: DataflowCtxt<'a, 'tcx>>
    PlaceObtainer<'state, 'a, 'tcx, Ctxt>
{
    fn weaken_place_from_read_upwards(
        &mut self,
        place: Place<'tcx>,
        debug_ctxt: &str,
    ) -> Result<(), PcgError> {
        if place.is_mut_ref(self.ctxt) {
            // We've reached an indirection (e.g from **s to *s), we
            // downgrade the ref from R to W
            // We need to continue: `s` would previously have capability R, which
            // is not compatible with it being mutably borrowed
            self.record_and_apply_action(
                    BorrowPcgAction::weaken(
                        place,
                        CapabilityKind::Read,
                        BlockType::DerefMutRefForExclusive.blocked_place_maximum_retained_capability(),
                        format!(
                            "{}: remove read permission upwards from base place {} (downgrade R to W for mut ref)",
                            debug_ctxt,
                            place.to_short_string(self.ctxt.bc_ctxt()),
                        ),
                        self.ctxt,
                    )
                    .into(),
                )?;
        } else {
            self.record_and_apply_action(
                BorrowPcgAction::weaken(
                    place,
                    CapabilityKind::Read,
                    None,
                    format!(
                        "{}: remove read permission upwards from base place {}",
                        debug_ctxt,
                        place.to_short_string(self.ctxt.bc_ctxt()),
                    ),
                    self.ctxt,
                )
                .into(),
            )?;
        }
        Ok(())
    }

    // Remove read permission upwards for strict ancestors of `place` Used when
    // we want to access `place` exclusively when activating a two-phase borrow
    // or when it is a postfix of a place that was downgraded to read
    // permission.
    pub(crate) fn remove_read_permission_upwards_and_label_rps(
        &mut self,
        place: Place<'tcx>,
        debug_ctxt: &str,
    ) -> Result<(), PcgError> {
        let place_regions = place.regions(self.ctxt);
        let mut prev = None;
        let mut current = place;
        while self.pcg.capabilities.get(current, self.ctxt) == Some(CapabilityKind::Read.into()) {
            self.weaken_place_from_read_upwards(current, debug_ctxt)?;
            let leaf_nodes = self.pcg.borrow.graph.frozen_graph().leaf_nodes(self.ctxt);
            for place in self.pcg.borrow.graph.places(self.ctxt) {
                if prev != Some(place)
                    && current.is_prefix_exact(place)
                    && leaf_nodes.contains(&place.into())
                    && self
                        .pcg
                        .capabilities
                        .get(place, self.ctxt)
                        .map(|c| c.expect_concrete())
                        == Some(CapabilityKind::Read)
                    && !place.projects_shared_ref(self.ctxt)
                {
                    self.record_and_apply_action(
                        BorrowPcgAction::restore_capability(
                            place,
                            CapabilityKind::Exclusive,
                            format!(
                                "{}: remove_read_permission_upwards_and_label_rps: restore exclusive cap for leaf place {}",
                                debug_ctxt,
                                place.to_short_string(self.ctxt.bc_ctxt())
                            ),
                        )
                        .into(),
                    )?;
                }
            }
            for r in place_regions.iter() {
                let current_rp = LifetimeProjection::new(*r, current, None, self.ctxt)?;
                if current.is_ref(self.ctxt)
                    && !current
                        .project_deref(self.ctxt)
                        .regions(self.ctxt)
                        .iter()
                        .contains(r)
                {
                    // If this region projection couldn't be modified (because its deref doesn't hold r), we skip
                    // There is probably a better way to do this
                    continue;
                }
                let edges_blocking_current_rp = self
                    .pcg
                    .borrow
                    .graph
                    .edges_blocking(current_rp.into(), self.ctxt)
                    .collect::<Vec<_>>();
                if !edges_blocking_current_rp.is_empty() {
                    let labelled_rp = current_rp
                        .with_label(Some(self.prev_snapshot_location().into()), self.ctxt);
                    let expansion_nodes = edges_blocking_current_rp
                        .iter()
                        .flat_map(|e| {
                            if let BorrowPcgEdgeKind::BorrowPcgExpansion(e) = e.kind()
                                && let PcgNode::LifetimeProjection(rp) = e.base
                                && rp == current_rp.into()
                            {
                                Some(
                                    e.expansion()
                                        .iter()
                                        .flat_map(|e| e.try_into_region_projection())
                                        .filter(|e| e.base.is_current())
                                        .collect::<Vec<_>>(),
                                )
                            } else {
                                None
                            }
                        })
                        .flatten()
                        .collect::<HashSet<_>>();
                    self.record_and_apply_action(
                        BorrowPcgAction::label_lifetime_projection(
                            LabelLifetimeProjectionPredicate::Equals(current_rp.into()),
                            Some(self.prev_snapshot_location().into()),
                            format!(
                                "{}: remove_read_permission_upwards_and_label_rps: label current lifetime projection {} with previous snapshot location {:?}",
                                debug_ctxt,
                                current_rp.to_short_string(self.ctxt.bc_ctxt()),
                                self.prev_snapshot_location()
                            ),
                        )
                        .into(),
                    )?;
                    // If the place is owned, we will never regain access to it,
                    // therefore future nodes aren't necessary
                    if !current.is_owned(self.ctxt) {
                        let future_rp = current_rp.with_placeholder_label(self.ctxt);
                        self.record_and_apply_action(
                            BorrowPcgAction::add_edge(
                                BorrowPcgEdge::new(
                                    BorrowFlowEdge::new(
                                        labelled_rp.into(),
                                        future_rp.into(),
                                        BorrowFlowEdgeKind::Future,
                                        self.ctxt,
                                    )
                                    .into(),
                                    self.pcg.borrow.validity_conditions.clone(),
                                ),
                                "remove_read_permission_upwards_and_label_rps",
                                self.ctxt,
                            )
                            .into(),
                        )?;
                        for expansion_node in expansion_nodes {
                            // If the expansion isn't labelled, it is likely a sibling RO of the place gaining exclusive capability
                            // so we connect to its current version
                            // Otherwise if its labelled we connect to its placeholder version
                            let to_connect = if expansion_node.label().is_none() {
                                expansion_node.into()
                            } else {
                                expansion_node.with_placeholder_label(self.ctxt).into()
                            };
                            self.record_and_apply_action(
                                BorrowPcgAction::add_edge(
                                    BorrowPcgEdge::new(
                                        BorrowFlowEdge::new(
                                            to_connect,
                                            future_rp.into(),
                                            BorrowFlowEdgeKind::Future,
                                            self.ctxt,
                                        )
                                        .into(),
                                        self.pcg.borrow.validity_conditions.clone(),
                                    ),
                                    "remove_read_permission_upwards_and_label_rps",
                                    self.ctxt,
                                )
                                .into(),
                            )?;
                        }
                    }
                }
            }
            let parent = match current.parent_place() {
                Some(parent) => parent,
                None => break,
            };
            prev = Some(current);
            current = parent;
        }
        Ok(())
    }
}
