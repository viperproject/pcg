// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use itertools::Itertools;

use crate::{
    combined_pcs::PcgError,
    free_pcs::{
        CapabilityKind, CapabilityLocal, CapabilityProjections, CapabilitySummary, RepackOp,
    },
    utils::{corrected::CorrectedPlace, PlaceRepacker},
};

pub trait RepackingBridgeSemiLattice<'tcx> {
    fn bridge(
        &self,
        other: &Self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> std::result::Result<Vec<RepackOp<'tcx>>, PcgError>;
}
impl<'tcx> RepackingBridgeSemiLattice<'tcx> for CapabilitySummary<'tcx> {
    fn bridge(
        &self,
        other: &Self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> std::result::Result<Vec<RepackOp<'tcx>>, PcgError> {
        if self.len() != other.len() {
            return Err(PcgError::internal(format!(
                "Capability summaries have different lengths: {} (previous) != {} (next)",
                self.len(),
                other.len()
            )));
        }
        let mut repacks = Vec::new();
        for (l, from) in self.iter_enumerated() {
            let local_repacks = from.bridge(&other[l], repacker)?;
            repacks.extend(local_repacks);
        }
        Ok(repacks)
    }
}

impl<'tcx> RepackingBridgeSemiLattice<'tcx> for CapabilityLocal<'tcx> {
    fn bridge(
        &self,
        other: &Self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> std::result::Result<Vec<RepackOp<'tcx>>, PcgError> {
        match (self, other) {
            (CapabilityLocal::Unallocated, CapabilityLocal::Unallocated) => Ok(Vec::new()),
            (CapabilityLocal::Allocated(from_places), CapabilityLocal::Allocated(to_places)) => {
                from_places.bridge(to_places, repacker)
            }
            (CapabilityLocal::Allocated(cps), CapabilityLocal::Unallocated) => {
                // TODO: remove need for clone
                let mut cps = cps.clone();
                let local = cps.get_local();
                let mut repacks = Vec::new();
                for (p, k) in cps.place_capabilities_mut() {
                    if *k > CapabilityKind::Write {
                        repacks.push(RepackOp::Weaken(*p, *k, CapabilityKind::Write));
                        *k = CapabilityKind::Write;
                    }
                }
                if cps.contains_expansion_from(local.into()) {
                    let packs = cps.collapse(local.into(), repacker).unwrap();
                    repacks.extend(packs);
                };
                repacks.push(RepackOp::StorageDead(local));
                Ok(repacks)
            }
            (CapabilityLocal::Unallocated, CapabilityLocal::Allocated(cps)) => {
                // A bit of an unusual case, should happen only when we
                // "allocated" a local to allow it to immediately be
                // StorageDead-ed. In this case we should ignore the SD.
                // assert_eq!(cps[&cps.get_local().into()], CapabilityKind::Write);
                Ok(vec![RepackOp::IgnoreStorageDead(cps.get_local())])
            }
        }
    }
}

impl<'tcx> RepackingBridgeSemiLattice<'tcx> for CapabilityProjections<'tcx> {
    fn bridge(
        &self,
        other: &Self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> std::result::Result<Vec<RepackOp<'tcx>>, PcgError> {
        let mut repacks = vec![];
        let mut from = self.clone();
        let other_expansions = other.expansions();
        'outer: loop {
            let from_expansions = from.expansions().clone();
            for (place, expansion) in from_expansions
                .into_iter()
                .sorted_by_key(|(p, _)| p.projection.len())
                .rev()
            {
                if let Some(other_expansion) = other_expansions.get(&place) {
                    if other_expansion != &expansion {
                        let collapse_repacks = from.collapse(place, repacker)?;
                        repacks.extend(collapse_repacks);
                        let expand_to = place.expansion_places(other_expansion, repacker)[0];
                        repacks.extend(from.expand(
                            place,
                            CorrectedPlace::new(expand_to, repacker),
                            from.get_capability(place).unwrap(),
                            repacker,
                        )?);
                        continue;
                    }
                } else {
                    repacks.extend(from.collapse(place, repacker)?);
                    continue 'outer;
                }
            }
            break;
        }
        for (place, expansion) in other
            .expansions()
            .iter()
            .sorted_by_key(|(p, _)| p.projection.len())
        {
            if !from.expansions().contains_key(place) {
                tracing::debug!("other expansion {:?} -> {:?}", place, expansion);
                tracing::debug!("from: {:?}", from);
                tracing::debug!("other: {:?}", other);
                repacks.extend(from.expand(
                    *place,
                    CorrectedPlace::new(place.expansion_places(expansion, repacker)[0], repacker),
                    from.get_capability(*place).unwrap(),
                    repacker,
                )?);
            }
        }
        Ok(repacks)
    }
}
