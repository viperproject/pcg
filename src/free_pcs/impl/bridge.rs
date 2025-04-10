// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use itertools::Itertools;

use crate::{
    free_pcs::{
        CapabilityKind, CapabilityLocal, CapabilityLocals, CapabilityProjections, RepackOp,
    },
    pcg::{
        place_capabilities::PlaceCapabilities,
        PcgError,
    },
    utils::{corrected::CorrectedPlace, maybe_old::MaybeOldPlace, CompilerCtxt},
};

impl<'tcx> CapabilityLocals<'tcx> {
    pub(crate) fn bridge(
        &self,
        other: &Self,
        place_capabilities: &PlaceCapabilities<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx,'_>,
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
            let local_repacks = from.bridge(&other[l], place_capabilities, repacker)?;
            repacks.extend(local_repacks);
        }
        Ok(repacks)
    }
}

impl<'tcx> CapabilityLocal<'tcx> {
    pub(crate) fn bridge(
        &self,
        other: &Self,
        place_capabilities: &PlaceCapabilities<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx,'_>,
    ) -> std::result::Result<Vec<RepackOp<'tcx>>, PcgError> {
        let mut place_capabilities = place_capabilities.clone();
        match (self, other) {
            (CapabilityLocal::Unallocated, CapabilityLocal::Unallocated) => Ok(Vec::new()),
            (CapabilityLocal::Allocated(from_places), CapabilityLocal::Allocated(to_places)) => {
                from_places.bridge(to_places, &place_capabilities, repacker)
            }
            (CapabilityLocal::Allocated(cps), CapabilityLocal::Unallocated) => {
                let mut cps = cps.clone();
                let local = cps.get_local();
                let mut repacks = Vec::new();
                for (p, k) in place_capabilities.owned_capabilities(local, repacker) {
                    if let MaybeOldPlace::Current { place } = p
                        && *k > CapabilityKind::Write
                    {
                        repacks.push(RepackOp::Weaken(place, *k, CapabilityKind::Write));
                        *k = CapabilityKind::Write;
                    }
                }
                if cps.contains_expansion_from(local.into()) {
                    let packs = cps
                        .collapse(local.into(), &mut place_capabilities, repacker)
                        .unwrap();
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

impl<'tcx> CapabilityProjections<'tcx> {
    pub(crate) fn bridge(
        &self,
        other: &Self,
        self_place_capabilities: &PlaceCapabilities<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx,'_>,
    ) -> std::result::Result<Vec<RepackOp<'tcx>>, PcgError> {
        let mut repacks = vec![];
        let mut from = self.clone();
        let other_expansions = other.expansions();
        let mut self_place_capabilities = self_place_capabilities.clone();
        'outer: loop {
            let from_expansions = from.expansions().clone();
            for (place, expansion) in from_expansions
                .into_iter()
                .sorted_by_key(|(p, _)| p.projection.len())
                .rev()
            {
                if let Some(other_expansion) = other_expansions.get(&place) {
                    if other_expansion != &expansion {
                        let collapse_repacks =
                            from.collapse(place, &mut self_place_capabilities, repacker)?;
                        repacks.extend(collapse_repacks);
                        let expand_to = place.expansion_places(other_expansion, repacker)[0];
                        repacks.extend(from.expand(
                            place,
                            CorrectedPlace::new(expand_to, repacker),
                            self_place_capabilities.get(place.into()).unwrap(),
                            &mut self_place_capabilities,
                            repacker,
                        )?);
                        continue;
                    }
                } else {
                    repacks.extend(from.collapse(place, &mut self_place_capabilities, repacker)?);
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
                    self_place_capabilities.get((*place).into()).unwrap(),
                    &mut self_place_capabilities,
                    repacker,
                )?);
            }
        }
        Ok(repacks)
    }
}
