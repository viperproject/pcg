use crate::{
    DebugLines,
    action::{BorrowPcgAction, PcgAction},
    borrow_pcg::action::LabelPlaceReason,
    capability_gte,
    owned_pcg::{
        ExpandedPlace, LocalExpansions, RepackExpand, RepackGuide, RepackOp,
        join::{data::JoinOwnedData, obtain::JoinObtainer},
    },
    pcg::{
        CapabilityKind, PcgError,
        ctxt::{self, AnalysisCtxt},
        obtain::{ActionApplier, HasSnapshotLocation, PlaceCollapser},
        place_capabilities::{PlaceCapabilities, PlaceCapabilitiesInterface},
    },
    pcg_validity_assert,
    utils::{
        CompilerCtxt, HasCompilerCtxt, Place, data_structures::HashSet,
        display::DisplayWithCompilerCtxt,
    },
};

enum JoinDifferentExpansionsResult<'tcx> {
    ExpandedForRead(RepackExpand<'tcx>),
    ExpandedForNoCapability,
    Collapsed(Vec<RepackOp<'tcx>>),
}

impl<'tcx> JoinDifferentExpansionsResult<'tcx> {
    fn actions(self) -> Vec<RepackOp<'tcx>> {
        match self {
            JoinDifferentExpansionsResult::ExpandedForRead(action) => {
                vec![RepackOp::Expand(action)]
            }
            JoinDifferentExpansionsResult::ExpandedForNoCapability => vec![],
            JoinDifferentExpansionsResult::Collapsed(actions) => actions,
        }
    }
}

enum JoinExpandedPlaceResult<'tcx> {
    JoinedWithSameExpansionInSelf(Vec<RepackOp<'tcx>>),
    CreatedExpansionFromSelf(Vec<RepackOp<'tcx>>),
    JoinedWithOtherExpansionsInSelf(JoinDifferentExpansionsResult<'tcx>),
}

impl<'tcx> JoinExpandedPlaceResult<'tcx> {
    fn actions(self) -> Vec<RepackOp<'tcx>> {
        match self {
            JoinExpandedPlaceResult::JoinedWithSameExpansionInSelf(actions) => actions,
            JoinExpandedPlaceResult::CreatedExpansionFromSelf(actions) => actions,
            JoinExpandedPlaceResult::JoinedWithOtherExpansionsInSelf(result) => result.actions(),
        }
    }

    fn performed_collapse(&self) -> bool {
        matches!(
            self,
            JoinExpandedPlaceResult::JoinedWithOtherExpansionsInSelf(
                JoinDifferentExpansionsResult::Collapsed(_)
            )
        )
    }
}

impl<'pcg, 'tcx> JoinOwnedData<'pcg, 'tcx, &'pcg mut LocalExpansions<'tcx>> {
    fn join_different_expansions_from_place<'other>(
        &mut self,
        other: &mut JoinOwnedData<'pcg, 'tcx, &'other mut LocalExpansions<'tcx>>,
        other_expansion: &ExpandedPlace<'tcx>,
        ctxt: AnalysisCtxt<'_, 'tcx>,
    ) -> Result<JoinDifferentExpansionsResult<'tcx>, PcgError>
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
            Ok(JoinDifferentExpansionsResult::ExpandedForRead(action))
        } else if other
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
                .insert_expansion(other_expansion.place, other_expansion.expansion.clone());
            return Ok(JoinDifferentExpansionsResult::ExpandedForNoCapability);
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

            return Ok(JoinDifferentExpansionsResult::Collapsed(
                self_obtainer.actions,
            ));
        }
    }

    fn expand_from_place_with_caps(
        &mut self,
        other: &mut JoinOwnedData<'pcg, 'tcx, &'pcg mut LocalExpansions<'tcx>>,
        expansion: &ExpandedPlace<'tcx>,
        self_cap: CapabilityKind,
        other_cap: CapabilityKind,
        ctxt: AnalysisCtxt<'_, 'tcx>,
    ) -> Result<Vec<RepackOp<'tcx>>, PcgError> {
        let place = expansion.place;
        let guide = expansion.guide();
        pcg_validity_assert!(!self.owned.contains_expansion_from(place));
        if let Some(expand_cap) = self_cap.minimum(other_cap) {
            tracing::info!(
                "Expanding from place {} with cap {:?}",
                place.to_short_string(ctxt.ctxt),
                expand_cap
            );
            let expand_action = RepackExpand::new(place, guide, expand_cap);
            self.owned
                .perform_expand_action(expand_action, self.capabilities, ctxt)?;
            let mut actions = vec![RepackOp::Expand(expand_action)];
            actions.extend(self.join_all_places_in_expansion(other, &expansion, ctxt)?);
            Ok(actions)
        } else if self_cap == CapabilityKind::Read {
            pcg_validity_assert!(other_cap == CapabilityKind::Write);
            tracing::info!(
                "No join expansion from place {}",
                place.to_short_string(ctxt.ctxt)
            );
            let actions = self.join_leaf_read_and_write_capabilities(other, place, ctxt)?;
            pcg_validity_assert!(!actions.is_empty());
            Ok(actions)
        } else {
            Ok(vec![])
        }
    }

    fn join_all_places_in_expansion(
        &mut self,
        other: &JoinOwnedData<'pcg, 'tcx, &'pcg mut LocalExpansions<'tcx>>,
        expansion: &ExpandedPlace<'tcx>,
        ctxt: AnalysisCtxt<'_, 'tcx>,
    ) -> Result<Vec<RepackOp<'tcx>>, PcgError> {
        let mut actions = vec![];
        for expansion_place in expansion.expansion_places(ctxt.ctxt).unwrap() {
            actions.extend(self.join_owned_places(other, expansion_place, ctxt)?);
        }
        Ok(actions)
    }

    fn join_other_expanded_place(
        &mut self,
        other: &mut JoinOwnedData<'pcg, 'tcx, &'pcg mut LocalExpansions<'tcx>>,
        other_expansion: &ExpandedPlace<'tcx>,
        ctxt: AnalysisCtxt<'_, 'tcx>,
    ) -> Result<JoinExpandedPlaceResult<'tcx>, PcgError> {
        tracing::info!("Joining expansion: {:?}", other_expansion);
        let place = other_expansion.place;
        let self_expansions = self
            .owned
            .expansions_from(place)
            .cloned()
            .collect::<HashSet<_>>();
        if self_expansions.contains(&other_expansion) {
            // If some of our expansions have leafs, we want to merge with the other ones
            // for example, to propagate read caps from the other borrowed places to our own
            Ok(JoinExpandedPlaceResult::JoinedWithSameExpansionInSelf(
                self.join_all_places_in_expansion(other, other_expansion, ctxt)?,
            ))
        } else if self_expansions.is_empty()
            && let Some(self_cap) = self.capabilities.get(place, ctxt.ctxt)
        {
            let other_cap = other.capabilities.get(place, ctxt.ctxt);
            tracing::info!("Self cap: {:?}, Other cap: {:?}", self_cap, other_cap);
            if let Some(other_cap) = other_cap {
                Ok(JoinExpandedPlaceResult::CreatedExpansionFromSelf(
                    self.expand_from_place_with_caps(
                        other,
                        other_expansion,
                        self_cap,
                        other_cap,
                        ctxt,
                    )?,
                ))
            } else {
                // We might as well just expand our place
                let expand_action = RepackExpand::new(place, other_expansion.guide(), self_cap);
                self.owned
                    .perform_expand_action(expand_action, self.capabilities, ctxt)?;
                Ok(JoinExpandedPlaceResult::CreatedExpansionFromSelf(vec![
                    RepackOp::Expand(expand_action),
                ]))
            }
        } else {
            Ok(JoinExpandedPlaceResult::JoinedWithOtherExpansionsInSelf(
                self.join_different_expansions_from_place(other, other_expansion, ctxt)?,
            ))
        }
    }

    fn join_expansions_iteration(
        &mut self,
        other: &mut JoinOwnedData<'pcg, 'tcx, &'pcg mut LocalExpansions<'tcx>>,
        ctxt: AnalysisCtxt<'_, 'tcx>,
    ) -> Result<Vec<RepackOp<'tcx>>, PcgError> {
        let expansions_shortest_first = other
            .owned
            .expansions_shortest_first()
            .cloned()
            .collect::<Vec<_>>();
        let mut actions: Vec<RepackOp<'tcx>> = vec![];
        let mut collapsed_places: HashSet<Place<'tcx>> = HashSet::default();
        for other_expansion in expansions_shortest_first {
            if collapsed_places
                .iter()
                .any(|p| p.is_prefix_of(other_expansion.place))
            {
                continue;
            }
            let result = self.join_other_expanded_place(other, &other_expansion, ctxt)?;
            let performed_collapse = result.performed_collapse();
            if performed_collapse {
                collapsed_places.insert(other_expansion.place);
            }
            actions.extend(result.actions());
        }
        Ok(actions)
    }

    fn join_expansions(
        &mut self,
        mut other: JoinOwnedData<'pcg, 'tcx, &'pcg mut LocalExpansions<'tcx>>,
        ctxt: AnalysisCtxt<'_, 'tcx>,
    ) -> Result<Vec<RepackOp<'tcx>>, PcgError> {
        let mut actions = vec![];
        let mut iteration = 0;
        loop {
            iteration += 1;
            tracing::info!("Iteration {}", iteration);
            let iteration_actions = self.join_expansions_iteration(&mut other, ctxt)?;
            if iteration_actions.is_empty() {
                break;
            } else {
                actions.extend(iteration_actions);
            }
        }
        Ok(actions)
    }

    fn render_debug_graph<'a, 'slf>(&'slf self, comment: &str, ctxt: impl HasCompilerCtxt<'a, 'tcx>)
    where
        'tcx: 'slf,
        'tcx: 'a,
    {
        self.borrows.graph.render_debug_graph(
            self.block,
            Some(crate::utils::DebugImgcat::JoinOwned),
            self.capabilities,
            comment,
            ctxt.ctxt(),
        );
    }

    fn join_leaf_read_and_write_capabilities<'mir>(
        &mut self,
        other: &JoinOwnedData<'pcg, 'tcx, &'pcg mut LocalExpansions<'tcx>>,
        place: Place<'tcx>,
        ctxt: AnalysisCtxt<'mir, 'tcx>,
    ) -> Result<Vec<RepackOp<'tcx>>, PcgError> {
        pcg_validity_assert!(self.owned.is_leaf_place(place, ctxt.ctxt));
        pcg_validity_assert!(other.owned.is_leaf_place(place, ctxt.ctxt));
        pcg_validity_assert!(self.capabilities.get(place, ctxt.ctxt) == Some(CapabilityKind::Read));
        pcg_validity_assert!(
            other.capabilities.get(place, ctxt.ctxt) == Some(CapabilityKind::Write)
        );
        let mut join_obtainer = JoinObtainer {
            ctxt,
            data: self,
            actions: vec![],
        };
        let action = BorrowPcgAction::label_place_and_update_related_capabilities(
            place,
            join_obtainer.prev_snapshot_location(),
            LabelPlaceReason::JoinOwnedReadAndWriteCapabilities,
        );
        join_obtainer.apply_action(PcgAction::Borrow(action))?;
        join_obtainer
            .data
            .capabilities
            .insert(place, CapabilityKind::Write, ctxt);
        Ok(join_obtainer.actions)
    }

    pub(crate) fn join_owned_places<'mir>(
        &mut self,
        other: &JoinOwnedData<'pcg, 'tcx, &'pcg mut LocalExpansions<'tcx>>,
        place: Place<'tcx>,
        ctxt: AnalysisCtxt<'mir, 'tcx>,
    ) -> Result<Vec<RepackOp<'tcx>>, PcgError> {
        if !self.owned.is_leaf_place(place, ctxt.ctxt)
            || !other.owned.is_leaf_place(place, ctxt.ctxt)
        {
            return Ok(vec![]);
        }
        let Some(self_cap) = self.capabilities.get(place, ctxt.ctxt) else {
            return Ok(vec![]);
        };
        let Some(other_cap) = other.capabilities.get(place, ctxt.ctxt) else {
            return Ok(vec![]);
        };
        match (self_cap, other_cap) {
            (capability_gte!(Read), CapabilityKind::Read) => {
                copy_read_capabilities(other.capabilities, self.capabilities, place, ctxt);
                Ok(vec![])
            }
            (CapabilityKind::Read, CapabilityKind::Write) => {
                self.join_leaf_read_and_write_capabilities(other, place, ctxt)
            }
            (CapabilityKind::Exclusive, CapabilityKind::Write) => {
                for (p, c) in other
                    .capabilities
                    .capabilities_for_strict_postfixes_of(place)
                {
                    self.capabilities.insert(p, c, ctxt);
                }
                Ok(vec![])
            }
            (CapabilityKind::Read | CapabilityKind::Write | CapabilityKind::Exclusive, _)
            | (CapabilityKind::ShallowExclusive, CapabilityKind::ShallowExclusive) => Ok(vec![]),
            (CapabilityKind::ShallowExclusive, _) => {
                todo!()
            }
        }
    }

    pub(crate) fn join<'mir>(
        mut self,
        mut other: JoinOwnedData<'pcg, 'tcx, &'pcg mut LocalExpansions<'tcx>>,
        ctxt: AnalysisCtxt<'mir, 'tcx>,
    ) -> Result<Vec<RepackOp<'tcx>>, PcgError> {
        let mut actions: Vec<RepackOp<'tcx>> = Vec::new();
        if self.owned.has_expansions() || other.owned.has_expansions() {
            actions.extend(other.reborrow().join_expansions(self.reborrow(), ctxt)?);
            self.render_debug_graph("Self After join_expansions (other)", ctxt);
            other.render_debug_graph("Other After join_expansions (other)", ctxt);
            actions.extend(self.reborrow().join_expansions(other.reborrow(), ctxt)?);
            self.render_debug_graph("Self After join_expansions (self)", ctxt);
            other.render_debug_graph("Other After join_expansions (self)", ctxt);
        } else {
            let place = Place::from(self.owned.get_local());
            actions.extend(self.reborrow().join_owned_places(&other, place, ctxt)?);
            actions.extend(other.join_owned_places(&self, place, ctxt)?);
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
    for (p, c) in cap_source.capabilities_for_strict_postfixes_of(place) {
        pcg_validity_assert!(c.is_read());
        cap_target.insert(p, c, ctxt);
    }
}
