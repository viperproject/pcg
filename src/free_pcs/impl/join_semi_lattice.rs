// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::rc::Rc;

use crate::combined_pcs::PcgError;
use itertools::Itertools;

use crate::{
    combined_pcs::EvalStmtPhase,
    free_pcs::{
        CapabilityLocal, CapabilityProjections, CapabilitySummary, FreePlaceCapabilitySummary,
    },
    utils::PlaceRepacker,
};

impl FreePlaceCapabilitySummary<'_, '_> {
    pub(crate) fn join(&mut self, other: &Self) -> Result<bool, PcgError> {
        let entry_state = Rc::<_>::make_mut(&mut self.data.entry_state);
        let other_state = other.data.unwrap(EvalStmtPhase::PostMain);
        match entry_state.as_mut() {
            Some(state) => state.join(other_state, self.repacker),
            None => {
                *entry_state = Some(other_state.clone());
                Ok(true)
            }
        }
    }
}

pub(crate) trait RepackingJoinSemiLattice<'tcx> {
    fn join(&mut self, other: &Self, repacker: PlaceRepacker<'_, 'tcx>) -> Result<bool, PcgError>;
}

impl<'tcx> RepackingJoinSemiLattice<'tcx> for CapabilitySummary<'tcx> {
    fn join(&mut self, other: &Self, repacker: PlaceRepacker<'_, 'tcx>) -> Result<bool, PcgError> {
        let mut changed = false;
        for (l, to) in self.iter_enumerated_mut() {
            let local_changed = to.join(&other[l], repacker)?;
            changed = changed || local_changed;
        }
        Ok(changed)
    }
}

impl<'tcx> RepackingJoinSemiLattice<'tcx> for CapabilityLocal<'tcx> {
    fn join(&mut self, other: &Self, repacker: PlaceRepacker<'_, 'tcx>) -> Result<bool, PcgError> {
        match (&mut *self, other) {
            (CapabilityLocal::Unallocated, CapabilityLocal::Unallocated) => Ok(false),
            (CapabilityLocal::Allocated(to_places), CapabilityLocal::Allocated(from_places)) => {
                to_places.join(from_places, repacker)
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

impl<'tcx> RepackingJoinSemiLattice<'tcx> for CapabilityProjections<'tcx> {
    fn join(&mut self, other: &Self, repacker: PlaceRepacker<'_, 'tcx>) -> Result<bool, PcgError> {
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
                        self.collapse(*place, repacker)?;
                        tracing::debug!("self: {:?}", self);
                        changed = true;
                        continue 'outer;
                    }
                } else if self.contains_expansion_to(*place, repacker) {
                    tracing::debug!("insert expansion {:?} -> {:?}", place, other_expansion);
                    tracing::debug!("other: {:?}", other);
                    self.insert_expansion(*place, other_expansion.clone());
                    if let Some(cap) = other.get_capability(*place) {
                        self.set_capability(*place, cap, repacker);
                    } else {
                        self.remove_capability(*place);
                    }
                    for place in place.expansion_places(other_expansion, repacker) {
                        if let Some(cap) = other.get_capability(place) {
                            self.set_capability(place, cap, repacker);
                        } else {
                            self.remove_capability(place);
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
