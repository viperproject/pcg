use crate::{
    DebugLines,
    action::{BorrowPcgAction, PcgAction},
    borrow_pcg::action::LabelPlaceReason,
    free_pcs::{
        CapabilityKind, ExpandedPlace, LocalExpansions, RepackExpand, RepackGuide, RepackOp,
        join::{data::JoinOwnedData, obtain::JoinObtainer},
    },
    pcg::{
        PcgError,
        ctxt::AnalysisCtxt,
        obtain::{ActionApplier, HasSnapshotLocation, PlaceCollapser},
        place_capabilities::{PlaceCapabilities, PlaceCapabilitiesInterface},
    },
    pcg_validity_assert,
    utils::{
        CompilerCtxt, HasCompilerCtxt, Place, data_structures::HashSet,
        display::DisplayWithCompilerCtxt,
    },
};

impl<'pcg: 'exp, 'exp, 'tcx> JoinOwnedData<'pcg, 'tcx, &'exp mut LocalExpansions<'tcx>> {
    fn join_expansions_from_place<'other>(
        &mut self,
        other: &mut JoinOwnedData<'pcg, 'tcx, &'other mut LocalExpansions<'tcx>>,
        other_expansion: ExpandedPlace<'tcx>,
        ctxt: AnalysisCtxt<'_, 'tcx>,
    ) -> Result<Vec<RepackOp<'tcx>>, PcgError>
    where
        'pcg: 'other,
    {
        let base_place = other_expansion.place;
        let self_cap = self.capabilities.get(base_place, ctxt.ctxt);
        let other_cap = other.capabilities.get(base_place, ctxt.ctxt);
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
                    ctxt.ctxt,
                )
            {
                // If this case holds, the leaf node is exclusively borrowed.
                // We want to insert this expansion (and all further expansions), without any capabilities
                tracing::debug!(
                    "Other expansions contain a descendent leaf node without capability for place {}",
                    base_place.to_short_string(ctxt.ctxt)
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
                self_obtainer.collapse_owned_places_and_lifetime_projections_to(
                    base_place,
                    CapabilityKind::Write,
                    format!(
                        "Join: collapse owned places {}",
                        other_expansion.place.to_short_string(ctxt.ctxt)
                    ),
                    ctxt.ctxt,
                )?;

                pcg_validity_assert!(
                    self_obtainer.data.capabilities.get(base_place, ctxt.ctxt)
                        == Some(CapabilityKind::Write),
                    "Expected capability for {} to be Write",
                    base_place.to_short_string(ctxt.ctxt)
                );

                let mut other_obtainer = JoinObtainer {
                    ctxt,
                    data: other,
                    actions: vec![],
                };

                other_obtainer.collapse_owned_places_and_lifetime_projections_to(
                    base_place,
                    CapabilityKind::Write,
                    format!(
                        "Join: collapse owned places {}",
                        other_expansion.place.to_short_string(ctxt.ctxt)
                    ),
                    ctxt.ctxt,
                )?;

                return Ok(self_obtainer.actions);
            }
        }
    }

    fn merge_owned_tree_leaf_places(
        &mut self,
        other: &mut JoinOwnedData<'pcg, 'tcx, &'exp mut LocalExpansions<'tcx>>,
        place: Place<'tcx>,
        ctxt: AnalysisCtxt<'_, 'tcx>,
    ) {
        if let Some(self_cap) = self.capabilities.get(place, ctxt.ctxt) {
            if self_cap >= CapabilityKind::Read
                && other.capabilities.get(place, ctxt.ctxt) == Some(CapabilityKind::Read)
            {
                copy_read_capabilities(&other.capabilities, &mut self.capabilities, place, ctxt);
            }
        }
    }

    fn expand_from_place_with_caps(
        &mut self,
        other: &mut JoinOwnedData<'pcg, 'tcx, &'exp mut LocalExpansions<'tcx>>,
        place: Place<'tcx>,
        guide: Option<RepackGuide>,
        self_cap: CapabilityKind,
        other_cap: CapabilityKind,
        ctxt: AnalysisCtxt<'_, 'tcx>,
    ) -> Result<Vec<RepackOp<'tcx>>, PcgError> {
        let mut actions = vec![];
        if let Some(expand_cap) = self_cap.minimum(other_cap) {
            tracing::info!(
                "Expanding from place {} with cap {:?}",
                place.to_short_string(ctxt.ctxt),
                expand_cap
            );
            let expand_action = RepackExpand::new(place, guide, expand_cap);
            self.owned
                .perform_expand_action(expand_action, self.capabilities, ctxt)?;
            actions.push(RepackOp::Expand(expand_action).into());
            let place_expansion = place.expansion(guide, ctxt.ctxt);
            for expansion_place in place.expansion_places(&place_expansion, ctxt.ctxt).unwrap() {
                if other
                    .owned
                    .leaf_places(ctxt.ctxt)
                    .contains(&expansion_place)
                {
                    self.merge_owned_tree_leaf_places(other, expansion_place, ctxt);
                }
            }
            return Ok(actions);
        } else {
            tracing::info!(
                "No join expansion from place {}",
                place.to_short_string(ctxt.ctxt)
            );
            // One has read, the other has write
            // We want to remove everything from the one with read
            let to_modify = if self_cap == CapabilityKind::Read {
                &mut *self
            } else {
                other
            };
            let mut join_obtainer = JoinObtainer {
                ctxt,
                data: to_modify,
                actions: vec![],
            };
            join_obtainer.label_and_remove_capabilities_for_deref_projections_of_postfix_places(
                place, false, ctxt.ctxt,
            )?;
            join_obtainer.collapse_owned_places_and_lifetime_projections_to(
                place,
                CapabilityKind::Read,
                "join".to_string(),
                ctxt.ctxt,
            )?;
            join_obtainer
                .data
                .capabilities
                .insert(place, CapabilityKind::Write, ctxt);
            actions.extend(join_obtainer.actions);
            pcg_validity_assert!(
                self.capabilities.get(place, ctxt.ctxt) == Some(CapabilityKind::Write)
            );
            pcg_validity_assert!(!actions.is_empty());
            return Ok(actions);
        }
    }

    fn join_expansions_iteration(
        &mut self,
        other: &mut JoinOwnedData<'pcg, 'tcx, &'exp mut LocalExpansions<'tcx>>,
        ctxt: AnalysisCtxt<'_, 'tcx>,
    ) -> Result<Vec<RepackOp<'tcx>>, PcgError> {
        let expansions_shortest_first = other
            .owned
            .expansions_shortest_first()
            .cloned()
            .collect::<Vec<_>>();
        let mut actions: Vec<RepackOp<'tcx>> = vec![];
        for other_expansion in expansions_shortest_first {
            tracing::info!("Joining expansion: {:?}", other_expansion);
            let place = other_expansion.place;
            let self_expansions = self
                .owned
                .expansions_from(place)
                .cloned()
                .collect::<HashSet<_>>();
            if self_expansions.contains(&other_expansion) {
                // If somem of our expansions have leafs, we want to merge with the other ones
                // for example, to propagate read caps from the other borrowed places to our own
                for expansion_place in place
                    .expansion_places(&other_expansion.expansion, ctxt.ctxt)
                    .unwrap()
                {
                    if self.owned.is_leaf_place(expansion_place, ctxt.ctxt)
                        && other.owned.is_leaf_place(expansion_place, ctxt.ctxt)
                    {
                        self.merge_owned_tree_leaf_places(other, expansion_place, ctxt);
                    }
                }
                continue;
            } else if self_expansions.is_empty() {
                let self_cap = self.capabilities.get(place, ctxt.ctxt);
                let other_cap = other.capabilities.get(place, ctxt.ctxt);
                tracing::info!("Self cap: {:?}, Other cap: {:?}", self_cap, other_cap);
                if let Some(self_cap) = self_cap {
                    if let Some(other_cap) = other_cap {
                        actions.extend(self.expand_from_place_with_caps(
                            other,
                            place,
                            other_expansion.guide(),
                            self_cap,
                            other_cap,
                            ctxt,
                        )?);
                    } else {
                        // We might as well just expand our place
                        let expand_action =
                            RepackExpand::new(place, other_expansion.guide(), self_cap);
                        self.owned
                            .perform_expand_action(expand_action, self.capabilities, ctxt)?;
                        actions.push(RepackOp::Expand(expand_action).into());
                    }
                    pcg_validity_assert!(!actions.is_empty());
                    // Short circuit here... we took an action in either branch
                    return Ok(actions);
                }
            } else {
                actions.extend(self.join_expansions_from_place(other, other_expansion, ctxt)?);
                pcg_validity_assert!(!actions.is_empty());
                // Short circuit here, we've looked at other expansions and should start over
                return Ok(actions);
            }
        }
        Ok(vec![])
    }

    fn join_expansions(
        &mut self,
        other: &mut JoinOwnedData<'pcg, 'tcx, &'exp mut LocalExpansions<'tcx>>,
        ctxt: AnalysisCtxt<'_, 'tcx>,
    ) -> Result<Vec<RepackOp<'tcx>>, PcgError> {
        let mut actions = vec![];
        let mut iteration = 0;
        loop {
            iteration += 1;
            tracing::info!("Iteration {}", iteration);
            let iteration_actions = self.join_expansions_iteration(other, ctxt)?;
            if iteration_actions.is_empty() {
                break;
            } else {
                actions.extend(iteration_actions);
            }
        }
        return Ok(actions);
    }

    fn render_debug_graph<'a, 'slf>(&'slf self, comment: &str, ctxt: impl HasCompilerCtxt<'a, 'tcx>)
    where
        'tcx: 'slf,
        'tcx: 'a
    {
        self.borrows.graph.render_debug_graph(
            self.block,
            Some(crate::utils::DebugImgcat::JoinOwned),
            &self.capabilities,
            comment,
            ctxt.ctxt(),
        );
    }

    pub(crate) fn join<'mir>(
        &mut self,
        mut other: JoinOwnedData<'pcg, 'tcx, &'exp mut LocalExpansions<'tcx>>,
        ctxt: AnalysisCtxt<'mir, 'tcx>,
    ) -> Result<Vec<RepackOp<'tcx>>, PcgError> {
        let mut actions: Vec<RepackOp<'tcx>> = Vec::new();
        if self.owned.has_expansions() || other.owned.has_expansions() {
            actions.extend(other.join_expansions(self, ctxt)?);
            self.render_debug_graph("Self After join_expansions (other)", ctxt);
            other.render_debug_graph("Other After join_expansions (other)", ctxt);
            actions.extend(self.join_expansions(&mut other, ctxt)?);
            self.render_debug_graph("Self After join_expansions (self)", ctxt);
            other.render_debug_graph("Other After join_expansions (self)", ctxt);
        } else {
            let local_place = Place::from(self.owned.get_local());
            if let Some(self_cap) = self.capabilities.get(local_place, ctxt.ctxt)
                && let Some(other_cap) = other.capabilities.get(local_place, ctxt.ctxt)
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
                    Some(CapabilityKind::Write) if self_cap != other_cap => {
                        // One has write, the other has exclusive
                        // The one having exclusive caps should have copy borrow caps from the write ones
                        let (source, target) = if self_cap == CapabilityKind::Write {
                            (&self.capabilities, &mut other.capabilities)
                        } else {
                            (&other.capabilities, &mut self.capabilities)
                        };
                        for (p, c) in source.capabilities_for_strict_postfixes_of(local_place) {
                            target.insert(p, c, ctxt);
                        }
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
                        let action = BorrowPcgAction::label_place_and_update_related_capabilities(
                            local_place,
                            join_obtainer.prev_snapshot_location(),
                            LabelPlaceReason::JoinOwnedReadAndWriteCapabilities,
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
            Place::from(self.owned.get_local()).to_short_string(ctxt.ctxt),
            actions.debug_lines(ctxt.ctxt).join("\n\t")
        );
        tracing::debug!(
            "Capabilities:\n\t{}",
            self.capabilities.debug_lines(ctxt.ctxt).join("\n\t")
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
    cap_source: &PlaceCapabilities<'tcx>,
    cap_target: &mut PlaceCapabilities<'tcx>,
    place: Place<'tcx>,
    ctxt: AnalysisCtxt<'_, 'tcx>,
) {
    cap_target.insert(place, CapabilityKind::Read, ctxt);
    for (p, c) in cap_source.capabilities_for_strict_postfixes_of(place.into()) {
        pcg_validity_assert!(c.is_read());
        cap_target.insert(p, c, ctxt);
    }
}
