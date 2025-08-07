use crate::{
    DebugLines,
    action::{BorrowPcgAction, PcgAction},
    borrow_pcg::action::LabelPlaceReason,
    free_pcs::{
        CapabilityKind, ExpandedPlace, LocalExpansions, RepackExpand, RepackOp,
        join::{data::JoinOwnedData, obtain::JoinObtainer},
    },
    pcg::{
        PcgError,
        obtain::{ActionApplier, HasSnapshotLocation, PlaceCollapser},
        place_capabilities::{PlaceCapabilities, PlaceCapabilitiesInterface},
    },
    pcg_validity_assert,
    utils::{CompilerCtxt, Place, data_structures::HashSet, display::DisplayWithCompilerCtxt},
};

impl<'pcg: 'exp, 'exp, 'tcx> JoinOwnedData<'pcg, 'tcx, &'exp mut LocalExpansions<'tcx>> {
    fn join_expansions_from_place<'other>(
        &mut self,
        other: &mut JoinOwnedData<'pcg, 'tcx, &'other mut LocalExpansions<'tcx>>,
        other_expansion: ExpandedPlace<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<Vec<RepackOp<'tcx>>, PcgError>
    where
        'pcg: 'other,
    {
        let base_place = other_expansion.place;
        let self_cap = self.capabilities.get(base_place, ctxt);
        let other_cap = other.capabilities.get(base_place, ctxt);
        if self_cap == Some(CapabilityKind::Read) && other_cap == Some(CapabilityKind::Read) {
            let action =
                RepackExpand::new(base_place, other_expansion.guide(), CapabilityKind::Read);
            self.owned
                .perform_expand_action(action, self.capabilities, ctxt)?;
            return Ok(vec![RepackOp::Expand(action).into()]);
        } else {
            if other
                .owned
                .contains_descendent_leaf_node_without_capability(
                    base_place,
                    other.capabilities,
                    ctxt,
                )
            {
                // If this case holds, the leaf node is exclusively borrowed.
                // We want to insert this expansion (and all further expansions), without any capabilities
                tracing::debug!(
                    "Other expansions contain a descendent leaf node without capability for place {}",
                    base_place.to_short_string(ctxt)
                );
                self.owned
                    .insert_expansion(other_expansion.place, other_expansion.expansion);
                return Ok(vec![]);
            } else {
                let mut self_obtainer = JoinObtainer {
                    ctxt,
                    data: self,
                    actions: vec![],
                };

                // The capability of the place should be Write because presumably something
                // was moved out in either of the expansions.
                self_obtainer.collapse_owned_places_to(
                    base_place,
                    CapabilityKind::Write,
                    format!(
                        "Join: collapse owned places {}",
                        other_expansion.place.to_short_string(ctxt)
                    ),
                    ctxt,
                )?;

                pcg_validity_assert!(
                    self_obtainer.data.capabilities.get(base_place, ctxt)
                        == Some(CapabilityKind::Write),
                    "Expected capability for {} to be Write",
                    base_place.to_short_string(ctxt)
                );

                let mut other_obtainer = JoinObtainer {
                    ctxt,
                    data: other,
                    actions: vec![],
                };

                other_obtainer.collapse_owned_places_to(
                    base_place,
                    CapabilityKind::Write,
                    format!(
                        "Join: collapse owned places {}",
                        other_expansion.place.to_short_string(ctxt)
                    ),
                    ctxt,
                )?;

                return Ok(self_obtainer.actions);
            }
        }
    }

    fn join_self_expansions_iteration(
        &mut self,
        other: &mut JoinOwnedData<'pcg, 'tcx, &mut LocalExpansions<'tcx>>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<Vec<RepackOp<'tcx>>, PcgError> {
        let expansions_shortest_first = self
            .owned
            .expansions_shortest_first()
            .cloned()
            .collect::<Vec<_>>();
        for self_expansion in expansions_shortest_first {
            if !other.owned.contains_expansion(&self_expansion)
                && let Some(other_cap) = other.capabilities.get(self_expansion.place, ctxt)
            {
                if let Some(CapabilityKind::Read) =
                    self.capabilities.get(self_expansion.place, ctxt)
                    && other_cap >= CapabilityKind::Read
                {
                    other.owned.perform_expand_action(
                        RepackExpand::new(
                            self_expansion.place,
                            self_expansion.guide(),
                            CapabilityKind::Read,
                        ),
                        other.capabilities,
                        ctxt,
                    )?;
                    for child_place in self_expansion.expansion_places(ctxt)? {
                        if self.owned.leaf_places(ctxt).contains(&child_place) {
                            for (p, c) in self
                                .capabilities
                                .capabilities_for_strict_postfixes_of(child_place)
                            {
                                other.capabilities.insert(p, c, ctxt);
                            }
                        }
                    }
                } else if self.capabilities.get(self_expansion.place, ctxt) == None {
                    match other_cap {
                        CapabilityKind::Exclusive => {
                            let expand_action = RepackExpand::new(
                                self_expansion.place,
                                self_expansion.guide(),
                                other_cap,
                            );
                            other.owned.perform_expand_action(
                                expand_action,
                                other.capabilities,
                                ctxt,
                            )?;
                        }
                        CapabilityKind::Write => {
                            let mut join_obtainer = JoinObtainer {
                                ctxt,
                                data: self,
                                actions: vec![],
                            };
                            join_obtainer.label_and_remove_capabilities_for_deref_projections_of_postfix_places(self_expansion.place, false, ctxt)?;
                            join_obtainer.restore_capability_to_leaf_places(
                                Some(self_expansion.place),
                                ctxt,
                            )?;
                            join_obtainer.collapse_owned_places_to(
                                self_expansion.place,
                                CapabilityKind::Write,
                                "join".to_string(),
                                ctxt,
                            )?;
                            return Ok(join_obtainer.actions);
                        }
                        _ => {}
                    }
                }
            }
        }
        Ok(vec![])
    }

    fn join_expansions(
        &mut self,
        other: &mut JoinOwnedData<'pcg, 'tcx, &mut LocalExpansions<'tcx>>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<Vec<RepackOp<'tcx>>, PcgError> {
        let mut actions = vec![];
        loop {
            let iteration_actions = self.join_self_expansions_iteration(other, ctxt)?;
            if iteration_actions.is_empty() {
                break;
            } else {
                actions.extend(iteration_actions);
            }
        }
        return Ok(actions);
    }

    pub(crate) fn join<'mir>(
        &mut self,
        mut other: JoinOwnedData<'pcg, 'tcx, &'exp mut LocalExpansions<'tcx>>,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> Result<Vec<RepackOp<'tcx>>, PcgError> {
        tracing::info!("Joining local expansions");
        let mut actions: Vec<RepackOp<'tcx>> = Vec::new();
        if self.owned.has_expansions() || other.owned.has_expansions() {
            actions.extend(other.join_expansions(self, ctxt)?);
            actions.extend(self.join_expansions(&mut other, ctxt)?);
        } else {
            let local_place = Place::from(self.owned.get_local());
            if let Some(self_cap) = self.capabilities.get(local_place, ctxt)
                && let Some(other_cap) = other.capabilities.get(local_place, ctxt)
            {
                match self_cap.minimum(other_cap) {
                    Some(CapabilityKind::Read) => {
                        // One or both has read cap, have all of the expansions be read
                        copy_read_capabilities(
                            &mut self.capabilities,
                            &mut other.capabilities,
                            local_place,
                            ctxt,
                        );
                        copy_read_capabilities(
                            &mut other.capabilities,
                            &mut self.capabilities,
                            local_place,
                            ctxt,
                        );
                    }
                    None => {
                        // One of these has read cap and the other has write cap
                        // We want to mark the read place as "old" and then set it to write
                        let mut join_obtainer: JoinObtainer<'pcg, '_, '_, 'mir, 'tcx> =
                            if self_cap.is_read() {
                                JoinObtainer {
                                    ctxt,
                                    data: self,
                                    actions: vec![],
                                }
                            } else {
                                JoinObtainer {
                                    ctxt,
                                    data: &mut other,
                                    actions: vec![],
                                }
                            };
                        let action = BorrowPcgAction::label_place(
                            local_place,
                            join_obtainer.prev_snapshot_location(),
                            LabelPlaceReason::MoveOut,
                        );
                        join_obtainer.apply_action(PcgAction::Borrow(action))?;
                        join_obtainer.data.capabilities.insert(
                            local_place,
                            CapabilityKind::Write,
                            ctxt,
                        );
                    }
                    _ => {
                        // Both are either W or E, in either case, neither will
                        // have any owned expansions
                    }
                }
            }
        }
        tracing::debug!(
            "Join {} actions:\n\t{}",
            Place::from(self.owned.get_local()).to_short_string(ctxt),
            actions.debug_lines(ctxt).join("\n\t")
        );
        tracing::debug!(
            "Capabilities:\n\t{}",
            self.capabilities.debug_lines(ctxt).join("\n\t")
        );
        Ok(actions)
    }
}

impl<'tcx> LocalExpansions<'tcx> {
    fn contains_descendent_leaf_node_without_capability(
        &self,
        place: Place<'tcx>,
        place_capabilities: &PlaceCapabilities<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.leaf_places(ctxt).into_iter().any(|p| {
            if place.is_prefix_of(p) && place_capabilities.get(p, ctxt).is_none() {
                tracing::debug!(
                    "Place {} is a leaf node without capability",
                    p.to_short_string(ctxt)
                );
                true
            } else {
                false
            }
        })
    }
}

fn copy_read_capabilities<'tcx>(
    cap_source: &mut PlaceCapabilities<'tcx>,
    cap_target: &mut PlaceCapabilities<'tcx>,
    place: Place<'tcx>,
    ctxt: CompilerCtxt<'_, 'tcx>,
) {
    cap_target.insert(place, CapabilityKind::Read, ctxt);
    for (p, c) in cap_source.capabilities_for_strict_postfixes_of(place.into()) {
        cap_target.insert(p, c, ctxt);
    }
}
