// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    action::OwnedPcgAction,
    borrow_pcg::{
        borrow_pcg_expansion::PlaceExpansion,
        state::{BorrowStateMutRef, BorrowsState, BorrowsStateLike},
    },
    free_pcs::{CapabilityKind, ExpandedPlace, RepackCollapse, RepackExpand, RepackOp},
    pcg::{
        PcgError,
        obtain::{HasSnapshotLocation, PlaceCollapser},
        place_capabilities::{PlaceCapabilities, PlaceCapabilitiesInterface},
    },
    pcg_validity_assert, pcg_validity_expect_some,
    utils::{Place, SnapshotLocation, data_structures::HashSet, display::DisplayWithCompilerCtxt},
};
use itertools::Itertools;

use crate::{
    free_pcs::{CapabilityLocal, CapabilityLocals, FreePlaceCapabilitySummary, LocalExpansions},
    rustc_interface::middle::mir,
    utils::CompilerCtxt,
};

impl<'tcx> FreePlaceCapabilitySummary<'tcx> {
    pub(crate) fn join(
        &mut self,
        other: &Self,
        self_block: mir::BasicBlock,
        self_place_capabilities: &mut PlaceCapabilities<'tcx>,
        other_place_capabilities: &mut PlaceCapabilities<'tcx>,
        borrows: &mut BorrowsState<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> Result<bool, PcgError> {
        self.data.as_mut().unwrap().join(
            other.data.as_ref().unwrap(),
            self_block,
            self_place_capabilities,
            other_place_capabilities,
            borrows,
            repacker,
        )
    }
}

impl<'tcx> CapabilityLocals<'tcx> {
    pub(crate) fn join(
        &mut self,
        other: &Self,
        self_block: mir::BasicBlock,
        self_place_capabilities: &mut PlaceCapabilities<'tcx>,
        other_place_capabilities: &mut PlaceCapabilities<'tcx>,
        borrows: &mut BorrowsState<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> Result<bool, PcgError> {
        let mut changed = false;
        for (l, to) in self.iter_enumerated_mut() {
            let local_changed = to.join(
                &other[l],
                self_block,
                self_place_capabilities,
                other_place_capabilities,
                borrows,
                repacker,
            )?;
            changed = changed || local_changed;
        }
        Ok(changed)
    }
}

impl<'tcx> CapabilityLocal<'tcx> {
    pub(crate) fn join(
        &mut self,
        other: &Self,
        self_block: mir::BasicBlock,
        self_place_capabilities: &mut PlaceCapabilities<'tcx>,
        other_place_capabilities: &mut PlaceCapabilities<'tcx>,
        borrows: &mut BorrowsState<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> Result<bool, PcgError> {
        match (&mut *self, other) {
            (CapabilityLocal::Unallocated, CapabilityLocal::Unallocated) => Ok(false),
            (CapabilityLocal::Allocated(to_places), CapabilityLocal::Allocated(from_places)) => {
                to_places.join(
                    from_places,
                    self_block,
                    self_place_capabilities,
                    other_place_capabilities,
                    borrows,
                    repacker,
                )?;
                Ok(true)
            }
            (CapabilityLocal::Allocated(..), CapabilityLocal::Unallocated) => {
                *self = CapabilityLocal::Unallocated;
                Ok(true)
            }
            // Can jump to a `is_cleanup` block with some paths being alloc and other not
            (CapabilityLocal::Unallocated, CapabilityLocal::Allocated(..)) => Ok(false),
        }
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

    fn contains_descendent_node_without_capability(
        &self,
        place: Place<'tcx>,
        place_capabilities: &PlaceCapabilities<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.leaves(ctxt)
            .into_iter()
            .any(|p| place.is_prefix_of(p) && place_capabilities.get(p).is_none())
    }

    fn perform_collapse_action(
        &mut self,
        collapse: RepackCollapse<'tcx>,
        place_capabilities: &mut PlaceCapabilities<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<(), PcgError> {
        let expansion_places = collapse.expansion_places(ctxt);
        let retained_cap = expansion_places
            .iter()
            .fold(CapabilityKind::Exclusive, |acc, place| {
                let removed_cap = place_capabilities.remove(*place, ctxt);
                let removed_cap = pcg_validity_expect_some!(
                    removed_cap,
                    CapabilityKind::Exclusive,
                    "Expected capability for {}",
                    place.to_short_string(ctxt)
                );
                let joined_cap = removed_cap.minimum(acc);
                pcg_validity_expect_some!(
                    joined_cap,
                    CapabilityKind::Exclusive,
                    "Cannot join capability {:?} and {:?}",
                    removed_cap,
                    acc,
                )
            });
        place_capabilities.insert(collapse.to, retained_cap, ctxt);
        Ok(())
    }

    fn join_expansions_from_place(
        &mut self,
        other: &mut Self,
        self_block: mir::BasicBlock,
        other_expansion: ExpandedPlace<'tcx>,
        self_expansions: HashSet<ExpandedPlace<'tcx>>,
        self_place_capabilities: &mut PlaceCapabilities<'tcx>,
        other_place_capabilities: &mut PlaceCapabilities<'tcx>,
        borrows: &mut BorrowsState<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<Vec<RepackOp<'tcx>>, PcgError> {
        let base_place = other_expansion.place;
        let self_cap = self_place_capabilities.get(base_place);
        let other_cap = other_place_capabilities.get(base_place);
        if self_cap == Some(CapabilityKind::Read) && other_cap == Some(CapabilityKind::Read) {
            let action =
                RepackExpand::new(base_place, other_expansion.guide(), CapabilityKind::Read);
            self.perform_expand_action(action, self_place_capabilities, ctxt)?;
            return Ok(vec![RepackOp::Expand(action).into()]);
        } else {
            if other.contains_descendent_node_without_capability(
                base_place,
                other_place_capabilities,
                ctxt,
            ) {
                self.insert_expansion(other_expansion.place, other_expansion.expansion);
                return Ok(vec![]);
            } else {
                struct JoinObtainer<'pcg, 'mir, 'tcx> {
                    ctxt: CompilerCtxt<'mir, 'tcx>,
                    self_block: mir::BasicBlock,
                    expansions: &'pcg mut LocalExpansions<'tcx>,
                    borrows: &'pcg mut BorrowsState<'tcx>,
                    self_place_capabilities: &'pcg mut PlaceCapabilities<'tcx>,
                    actions: Vec<RepackOp<'tcx>>,
                }

                impl<'pcg, 'mir, 'tcx> HasSnapshotLocation for JoinObtainer<'pcg, 'mir, 'tcx> {
                    fn prev_snapshot_location(&self) -> SnapshotLocation {
                        SnapshotLocation::BeforeJoin(self.self_block)
                    }
                }

                impl<'pcg, 'mir, 'tcx> PlaceCollapser<'mir, 'tcx> for JoinObtainer<'pcg, 'mir, 'tcx> {
                    fn get_local_expansions(&self, local: mir::Local) -> &LocalExpansions<'tcx> {
                        self.expansions
                    }

                    fn perform_collapse_action(
                        &mut self,
                        collapse: crate::free_pcs::RepackCollapse<'tcx>,
                    ) -> Result<(), PcgError> {
                        self.expansions.perform_collapse_action(
                            collapse,
                            self.self_place_capabilities,
                            self.ctxt,
                        )?;
                        self.actions.push(RepackOp::Collapse(collapse).into());
                        Ok(())
                    }

                    fn perform_add_edge_action(
                        &mut self,
                        edge: crate::borrow_pcg::borrow_pcg_edge::BorrowPcgEdge<'tcx>,
                    ) -> Result<(), PcgError> {
                        self.borrows.graph_mut().insert(edge, self.ctxt);
                        Ok(())
                    }

                    fn borrows_state(&mut self) -> BorrowStateMutRef<'_, 'tcx> {
                        self.borrows.into()
                    }
                }

                return Ok(vec![]);
            }
        }
    }

    pub(crate) fn join(
        &mut self,
        other: &Self,
        self_block: mir::BasicBlock,
        self_place_capabilities: &mut PlaceCapabilities<'tcx>,
        other_place_capabilities: &mut PlaceCapabilities<'tcx>,
        borrows: &mut BorrowsState<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<Vec<RepackOp<'tcx>>, PcgError> {
        let mut other = other.clone();
        let mut actions: Vec<RepackOp<'tcx>> = Vec::new();
        loop {
            let mut other_expansions = other
                .expansions_shortest_first()
                .cloned()
                .collect::<Vec<_>>();
            while let Some(other_expansion) = other_expansions.pop() {
                let self_expansions = self
                    .expansions_from(other_expansion.place)
                    .cloned()
                    .collect::<HashSet<_>>();
                if self_expansions.contains(&other_expansion) {
                    continue;
                } else if self_expansions.is_empty() {
                    let other_expansion_guide = other_expansion.guide();
                    if self.is_leaf(other_expansion.place, ctxt) {
                        if let Some(cap) = self_place_capabilities.get(other_expansion.place) {
                            let expand_action = RepackExpand::new(
                                other_expansion.place,
                                other_expansion_guide,
                                cap,
                            );
                            self.perform_expand_action(
                                expand_action,
                                self_place_capabilities,
                                ctxt,
                            )?;
                            actions.push(RepackOp::Expand(expand_action).into());
                        }
                    }
                } else {
                    actions.extend(self.join_expansions_from_place(
                        &mut other,
                        self_block,
                        other_expansion.clone(),
                        self_expansions,
                        self_place_capabilities,
                        other_place_capabilities,
                        borrows,
                        ctxt,
                    )?);
                    continue;
                }
            }
            break;
        }
        for self_expansion in self.expansions_shortest_first() {
            if !other.contains_expansion(self_expansion) {
                if let Some(CapabilityKind::Read) =
                    self_place_capabilities.get(self_expansion.place)
                    && let Some(other_cap) = other_place_capabilities.get(self_expansion.place)
                    && other_cap >= CapabilityKind::Read
                {
                    other.perform_expand_action(
                        RepackExpand::new(
                            self_expansion.place,
                            self_expansion.guide(),
                            CapabilityKind::Read,
                        ),
                        other_place_capabilities,
                        ctxt,
                    )?;
                }
            }
        }
        Ok(actions)
    }
}
