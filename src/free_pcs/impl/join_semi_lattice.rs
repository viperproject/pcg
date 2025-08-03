// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    action::OwnedPcgAction,
    borrow_pcg::borrow_pcg_expansion::PlaceExpansion,
    free_pcs::{CapabilityKind, ExpandedPlace, RepackExpand, RepackOp},
    pcg::{
        PcgError,
        place_capabilities::{PlaceCapabilities, PlaceCapabilitiesInterface},
    },
    pcg_validity_assert,
    utils::{Place, display::DisplayWithCompilerCtxt},
};
use itertools::Itertools;

use crate::{
    free_pcs::{CapabilityLocal, CapabilityLocals, FreePlaceCapabilitySummary, LocalExpansions},
    utils::CompilerCtxt,
};

impl<'tcx> FreePlaceCapabilitySummary<'tcx> {
    pub(crate) fn join(
        &mut self,
        other: &Self,
        self_place_capabilities: &mut PlaceCapabilities<'tcx>,
        other_place_capabilities: &mut PlaceCapabilities<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> Result<bool, PcgError> {
        self.data.as_mut().unwrap().join(
            other.data.as_ref().unwrap(),
            self_place_capabilities,
            other_place_capabilities,
            repacker,
        )
    }
}

impl<'tcx> CapabilityLocals<'tcx> {
    pub(crate) fn join(
        &mut self,
        other: &Self,
        self_place_capabilities: &mut PlaceCapabilities<'tcx>,
        other_place_capabilities: &mut PlaceCapabilities<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> Result<bool, PcgError> {
        let mut changed = false;
        for (l, to) in self.iter_enumerated_mut() {
            let local_changed = to.join(
                &other[l],
                self_place_capabilities,
                other_place_capabilities,
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
        self_place_capabilities: &mut PlaceCapabilities<'tcx>,
        other_place_capabilities: &mut PlaceCapabilities<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> Result<bool, PcgError> {
        match (&mut *self, other) {
            (CapabilityLocal::Unallocated, CapabilityLocal::Unallocated) => Ok(false),
            (CapabilityLocal::Allocated(to_places), CapabilityLocal::Allocated(from_places)) => {
                to_places.join(
                    from_places,
                    self_place_capabilities,
                    other_place_capabilities,
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

    pub(crate) fn join(
        &mut self,
        other: &Self,
        self_place_capabilities: &mut PlaceCapabilities<'tcx>,
        other_place_capabilities: &mut PlaceCapabilities<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<Vec<RepackOp<'tcx>>, PcgError> {
        let mut other = other.clone();
        let mut actions = Vec::new();
        for other_expansion in other.expansions_shortest_first() {
            if !self.contains_expansion(other_expansion) {
                let other_expansion_guide = other_expansion.guide();
                if self.is_leaf(other_expansion.place, ctxt) {
                    if let Some(cap) = self_place_capabilities.get(other_expansion.place) {
                        let expand_action =
                            RepackExpand::new(other_expansion.place, other_expansion_guide, cap);
                        self.perform_expand_action(expand_action, self_place_capabilities, ctxt)?;
                        actions.push(RepackOp::Expand(expand_action).into());
                    }
                }
            }
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
