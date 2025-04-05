// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::pcg::{place_capabilities::PlaceCapabilities, PcgError};
use itertools::Itertools;

use crate::{
    free_pcs::{
        CapabilityLocal, CapabilityLocals, CapabilityProjections, FreePlaceCapabilitySummary,
    },
    utils::CompilerCtxt,
};

impl<'tcx> FreePlaceCapabilitySummary<'tcx> {
    pub(crate) fn join(
        &mut self,
        other: &Self,
        self_place_capabilities: &mut PlaceCapabilities<'tcx>,
        other_place_capabilities: &PlaceCapabilities<'tcx>,
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
        other_place_capabilities: &PlaceCapabilities<'tcx>,
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
        other_place_capabilities: &PlaceCapabilities<'tcx>,
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
                )
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

impl<'tcx> CapabilityProjections<'tcx> {
    pub(crate) fn join(
        &mut self,
        other: &Self,
        self_place_capabilities: &mut PlaceCapabilities<'tcx>,
        other_place_capabilities: &PlaceCapabilities<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> Result<bool, PcgError> {
        let mut changed = false;
        'outer: loop {
            let expansions = self.expansions().clone();
            for (place, other_expansion) in other
                .expansions()
                .iter()
                .sorted_by_key(|(p, _)| p.projection.len())
            {
                if let Some(self_expansion) = expansions.get(place) {
                    if other_expansion != self_expansion {
                        tracing::debug!("collapse to {:?}", place);
                        self.collapse(*place, self_place_capabilities, repacker)?;
                        tracing::debug!("self: {:?}", self);
                        changed = true;
                        continue 'outer;
                    }
                } else if self.contains_expansion_to(*place, repacker) {
                    tracing::debug!("insert expansion {:?} -> {:?}", place, other_expansion);
                    tracing::debug!("other: {:?}", other);
                    self.insert_expansion(*place, other_expansion.clone());
                    if let Some(cap) = other_place_capabilities.get((*place).into()) {
                        self_place_capabilities.insert((*place).into(), cap);
                    } else {
                        self_place_capabilities.remove((*place).into());
                    }
                    for place in place.expansion_places(other_expansion, repacker) {
                        if let Some(cap) = other_place_capabilities.get(place.into()) {
                            self_place_capabilities.insert(place.into(), cap);
                        } else {
                            self_place_capabilities.remove(place.into());
                        }
                    }
                    changed = true;
                    continue 'outer;
                }
                // Otherwise, this is an expansion from a place that won't survive the join
            }
            break;
        }
        tracing::debug!("self: {:?}", self);
        Ok(changed)
    }
}
