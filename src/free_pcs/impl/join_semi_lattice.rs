// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    DebugLines,
    action::OwnedPcgAction,
    borrow_pcg::{
        borrow_pcg_expansion::PlaceExpansion,
        state::{BorrowStateMutRef, BorrowsState, BorrowsStateLike},
    },
    free_pcs::{CapabilityKind, ExpandedPlace, RepackCollapse, RepackExpand, RepackOp},
    pcg::{
        PcgError, PcgMutRef,
        obtain::{HasSnapshotLocation, PlaceCollapser},
        place_capabilities::{PlaceCapabilities, PlaceCapabilitiesInterface},
    },
    pcg_validity_assert, pcg_validity_expect_some,
    utils::{Place, SnapshotLocation, data_structures::HashSet, display::DisplayWithCompilerCtxt},
};
use itertools::Itertools;

use crate::{
    free_pcs::{LocalExpansions, OwnedPcg, OwnedPcgData, OwnedPcgLocal},
    rustc_interface::middle::mir,
    utils::CompilerCtxt,
};

impl<'pcg, 'tcx> JoinOwnedData<'pcg, 'tcx, &'pcg mut OwnedPcgLocal<'tcx>> {
    pub(crate) fn join(
        &mut self,
        mut other: JoinOwnedData<'pcg, 'tcx, &'pcg OwnedPcgLocal<'tcx>>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<bool, PcgError> {
        match (&mut self.owned, &mut other.owned) {
            (OwnedPcgLocal::Unallocated, OwnedPcgLocal::Unallocated) => Ok(false),
            (OwnedPcgLocal::Allocated(to_places), OwnedPcgLocal::Allocated(from_places)) => {
                let mut self_allocated = JoinOwnedData {
                    owned: to_places,
                    borrows: self.borrows,
                    capabilities: self.capabilities,
                    block: self.block,
                };
                let other_allocated = other.map_owned(|_| from_places.clone());
                self_allocated.join(other_allocated, ctxt)?;
                Ok(true)
            }
            (OwnedPcgLocal::Allocated(..), OwnedPcgLocal::Unallocated) => {
                *self.owned = OwnedPcgLocal::Unallocated;
                Ok(true)
            }
            // Can jump to a `is_cleanup` block with some paths being alloc and other not
            (OwnedPcgLocal::Unallocated, OwnedPcgLocal::Allocated(..)) => Ok(false),
        }
    }
}

pub(crate) struct JoinOwnedData<'pcg, 'tcx, T> {
    pub(crate) owned: T,
    pub(crate) borrows: &'pcg mut BorrowsState<'tcx>,
    pub(crate) capabilities: &'pcg mut PlaceCapabilities<'tcx>,
    pub(crate) block: mir::BasicBlock,
}

impl<'pcg: 'owned, 'tcx, 'owned, T: 'owned> JoinOwnedData<'pcg, 'tcx, T> {
    pub(crate) fn map_owned<'slf: 'res, 'res, U: 'res>(
        &'slf mut self,
        f: impl Fn(&'slf mut T) -> U,
    ) -> JoinOwnedData<'res, 'tcx, U>
    where
        'pcg: 'res,
    {
        JoinOwnedData {
            owned: f(&mut self.owned),
            borrows: &mut self.borrows,
            capabilities: &mut self.capabilities,
            block: self.block,
        }
    }
}

impl<'pcg, 'tcx> JoinOwnedData<'pcg, 'tcx, &'pcg mut OwnedPcg<'tcx>> {
    pub(crate) fn join(
        &mut self,
        mut other: JoinOwnedData<'pcg, 'tcx, &'pcg OwnedPcg<'tcx>>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<bool, PcgError> {
        let mut owned_pcg_data = self.map_owned(|owned| owned.locals_mut());
        let mut other_owned_pcg_data = other.map_owned(|owned| owned.locals());
        let mut changed = false;
        for local in 0..owned_pcg_data.owned.num_locals() {
            let local: mir::Local = local.into();
            let mut owned_local_data =
                owned_pcg_data.map_owned(|owned| owned.get_mut(local).unwrap());
            let other_owned_local_data =
                other_owned_pcg_data.map_owned(|owned| owned.get(local).unwrap());
            let local_changed = owned_local_data.join(other_owned_local_data, ctxt)?;
            changed = changed || local_changed;
        }
        Ok(changed)
    }
}

struct JoinObtainer<'pcg: 'exp, 'exp, 'slf, 'mir, 'tcx> {
    ctxt: CompilerCtxt<'mir, 'tcx>,
    data: &'slf mut JoinOwnedData<'pcg, 'tcx, &'exp mut LocalExpansions<'tcx>>,
    actions: Vec<RepackOp<'tcx>>,
}

impl HasSnapshotLocation for JoinObtainer<'_, '_, '_, '_, '_> {
    fn prev_snapshot_location(&self) -> SnapshotLocation {
        SnapshotLocation::BeforeJoin(self.data.block)
    }
}

impl<'pcg, 'mir, 'tcx> PlaceCollapser<'mir, 'tcx> for JoinObtainer<'_, '_, '_, 'mir, 'tcx> {
    fn get_local_expansions(&self, _local: mir::Local) -> &LocalExpansions<'tcx> {
        &self.data.owned
    }

    fn perform_collapse_action(
        &mut self,
        collapse: crate::free_pcs::RepackCollapse<'tcx>,
        context: &str,
    ) -> Result<(), PcgError> {
        self.data
            .owned
            .perform_collapse_action(collapse, self.data.capabilities, self.ctxt)?;
        self.actions.push(RepackOp::Collapse(collapse).into());
        Ok(())
    }

    fn perform_add_edge_action(
        &mut self,
        edge: crate::borrow_pcg::borrow_pcg_edge::BorrowPcgEdge<'tcx>,
    ) -> Result<(), PcgError> {
        self.data.borrows.graph_mut().insert(edge, self.ctxt);
        Ok(())
    }

    fn borrows_state(&mut self) -> BorrowStateMutRef<'_, 'tcx> {
        self.data.borrows.into()
    }
}

impl<'pcg, 'tcx> JoinOwnedData<'pcg, 'tcx, &'pcg mut LocalExpansions<'tcx>> {
    fn join_expansions_from_place<'other>(
        &mut self,
        other: &mut JoinOwnedData<'pcg, 'tcx, &'other mut LocalExpansions<'tcx>>,
        other_expansion: ExpandedPlace<'tcx>,
        self_expansions: HashSet<ExpandedPlace<'tcx>>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<Vec<RepackOp<'tcx>>, PcgError>
    where
        'pcg: 'other,
    {
        let base_place = other_expansion.place;
        let self_cap = self.capabilities.get(base_place);
        let other_cap = other.capabilities.get(base_place);
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
                    self_obtainer.data.capabilities.get(base_place) == Some(CapabilityKind::Write),
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
    pub(crate) fn join(
        &mut self,
        mut other: JoinOwnedData<'pcg, 'tcx, LocalExpansions<'tcx>>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<Vec<RepackOp<'tcx>>, PcgError> {
        let mut actions: Vec<RepackOp<'tcx>> = Vec::new();
        let mut other = JoinOwnedData {
            owned: &mut other.owned,
            borrows: other.borrows,
            capabilities: other.capabilities,
            block: other.block,
        };
        'outer: loop {
            // We get by longest expansions first but then use `pop`, so in
            // practice we observe the shortest expansions first
            let mut other_expansions = other
                .owned
                .expansions_longest_first()
                .cloned()
                .collect::<Vec<_>>();
            while let Some(other_expansion) = other_expansions.pop() {
                let self_expansions = self
                    .owned
                    .expansions_from(other_expansion.place)
                    .cloned()
                    .collect::<HashSet<_>>();
                if self_expansions.contains(&other_expansion) {
                    tracing::debug!(
                        "Skipping expansion {:?} because it is already in the local expansions",
                        other_expansion
                    );
                    continue;
                } else if self_expansions.is_empty() {
                    tracing::debug!("Expansion {:?} is not in self", other_expansion);
                    let other_expansion_guide = other_expansion.guide();
                    if self.owned.is_leaf(other_expansion.place, ctxt) {
                        if let Some(cap) = self.capabilities.get(other_expansion.place) {
                            let expand_action = RepackExpand::new(
                                other_expansion.place,
                                other_expansion_guide,
                                cap,
                            );
                            self.owned.perform_expand_action(
                                expand_action,
                                self.capabilities,
                                ctxt,
                            )?;
                            actions.push(RepackOp::Expand(expand_action).into());
                        }
                    }
                } else {
                    actions.extend(self.join_expansions_from_place(
                        &mut other,
                        other_expansion.clone(),
                        self_expansions,
                        ctxt,
                    )?);
                    continue 'outer;
                }
            }
            break;
        }
        'outer: loop {
            let expansions_shortest_first = self
                .owned
                .expansions_shortest_first()
                .cloned()
                .collect::<Vec<_>>();
            for self_expansion in expansions_shortest_first {
                if !other.owned.contains_expansion(&self_expansion)
                    && let Some(other_cap) = other.capabilities.get(self_expansion.place)
                {
                    if let Some(CapabilityKind::Read) = self.capabilities.get(self_expansion.place)
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
                    } else if self.capabilities.get(self_expansion.place) == None {
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
                                join_obtainer.collapse_owned_places_to(
                                    self_expansion.place,
                                    CapabilityKind::Write,
                                    "join".to_string(),
                                    ctxt,
                                )?;
                                actions.extend(join_obtainer.actions);
                                continue 'outer;
                            }
                            _ => {}
                        }
                    }
                }
            }
            break;
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
    pub(crate) fn contains_expansion(&self, expansion: &ExpandedPlace<'tcx>) -> bool {
        self.expansions.iter().any(|ep| ep == expansion)
    }

    pub(crate) fn expansions_shortest_first(&self) -> impl Iterator<Item = &ExpandedPlace<'tcx>> {
        self.expansions
            .iter()
            .sorted_by_key(|ep| ep.place.projection().len())
    }

    pub(crate) fn expansions_longest_first(&self) -> impl Iterator<Item = &ExpandedPlace<'tcx>> {
        self.expansions
            .iter()
            .sorted_by_key(|ep| ep.place.projection().len())
            .rev()
    }

    pub(crate) fn is_leaf(&self, place: Place<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        self.leaves(ctxt).contains(&place)
    }

    pub(crate) fn perform_expand_action(
        &mut self,
        expand: RepackExpand<'tcx>,
        capabilities: &mut PlaceCapabilities<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<(), PcgError> {
        let target_places = expand.target_places(ctxt);
        self.insert_expansion(
            expand.from,
            PlaceExpansion::from_places(target_places.clone(), ctxt),
        );
        let source_cap = if expand.capability.is_read() {
            expand.capability
        } else {
            capabilities.get(expand.from).unwrap_or_else(|| {
                pcg_validity_assert!(false, "no cap for {}", expand.from.to_short_string(ctxt));
                // panic!("no cap for {}", expand.from.to_short_string(ctxt));
                // For debugging, assume exclusive, we can visualize the graph to see what's going on
                CapabilityKind::Exclusive
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

    fn contains_descendent_leaf_node_without_capability(
        &self,
        place: Place<'tcx>,
        place_capabilities: &PlaceCapabilities<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.leaves(ctxt).into_iter().any(|p| {
            if place.is_prefix_of(p) && place_capabilities.get(p).is_none() {
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

    pub(crate) fn all_descendants_of(
        &self,
        place: Place<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> HashSet<Place<'tcx>> {
        self.expansions
            .iter()
            .filter(|ep| place.is_prefix_of(ep.place))
            .flat_map(|ep| ep.expansion_places(ctxt))
            .collect()
    }

    pub(crate) fn all_children_of(
        &self,
        place: Place<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> HashSet<Place<'tcx>> {
        self.expansions
            .iter()
            .filter(|ep| ep.place == place)
            .flat_map(|ep| ep.expansion_places(ctxt))
            .collect()
    }

    pub(crate) fn get_retained_capability_of_children(
        &self,
        place: Place<'tcx>,
        capabilities: &PlaceCapabilities<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Option<CapabilityKind> {
        let children = self.all_children_of(place, ctxt);
        let mut current_cap = CapabilityKind::Exclusive;
        for child in children {
            let child_cap = capabilities.get(child)?;
            current_cap = current_cap.minimum(child_cap)?;
        }
        Some(current_cap)
    }

    pub(crate) fn perform_collapse_action(
        &mut self,
        collapse: RepackCollapse<'tcx>,
        place_capabilities: &mut PlaceCapabilities<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<(), PcgError> {
        let expansion_places = self.all_children_of(collapse.to, ctxt);
        let retained_cap = expansion_places
            .iter()
            .fold(CapabilityKind::Exclusive, |acc, place| {
                let removed_cap = place_capabilities.remove(*place, ctxt);
                let removed_cap = pcg_validity_expect_some!(
                    removed_cap,
                    CapabilityKind::Exclusive,
                    [ctxt],
                    "Expected capability for {}",
                    place.to_short_string(ctxt)
                );
                pcg_validity_assert!(
                    removed_cap >= collapse.capability,
                    "Expected removed cap {:?} for {} to be at least {:?}",
                    removed_cap,
                    place.to_short_string(ctxt),
                    collapse.capability
                );
                let joined_cap = removed_cap.minimum(acc);
                pcg_validity_expect_some!(
                    joined_cap,
                    CapabilityKind::Exclusive,
                    [ctxt],
                    "Cannot join capability {:?} and {:?}",
                    removed_cap,
                    acc,
                )
            });
        pcg_validity_assert!(
            retained_cap >= collapse.capability,
            "Expected retained cap {:?} to be at least {:?}",
            retained_cap,
            collapse.capability
        );
        self.remove_all_expansions_from(collapse.to, ctxt);
        place_capabilities.insert(collapse.to, retained_cap, ctxt);
        Ok(())
    }
}
