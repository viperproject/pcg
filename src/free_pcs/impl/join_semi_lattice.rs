// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    borrow_pcg::borrow_pcg_expansion::PlaceExpansion, free_pcs::{
        join::data::JoinOwnedData, CapabilityKind, ExpandedPlace, RepackCollapse, RepackExpand
    }, pcg::{
        place_capabilities::{PlaceCapabilities, PlaceCapabilitiesInterface}, PcgError
    }, pcg_validity_assert, pcg_validity_expect_some, utils::{data_structures::HashSet, display::DisplayWithCompilerCtxt, Place}
};
use itertools::Itertools;

use crate::{
    free_pcs::{LocalExpansions, OwnedPcg, OwnedPcgLocal},
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
                let mut from_places = from_places.clone();
                let other_allocated = JoinOwnedData {
                    owned: &mut from_places,
                    borrows: other.borrows,
                    capabilities: other.capabilities,
                    block: other.block,
                };
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
        self.leaf_places(ctxt).contains(&place)
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


    pub(crate) fn all_descendants_of(
        &self,
        place: Place<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> HashSet<Place<'tcx>> {
        self.expansions
            .iter()
            .filter(|ep| place.is_prefix_of(ep.place))
            .flat_map(|ep| ep.expansion_places(ctxt).unwrap())
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
            .flat_map(|ep| ep.expansion_places(ctxt).unwrap())
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
                    fallback: CapabilityKind::Exclusive,
                    [ctxt],
                    "Expected capability for {}",
                    place.to_short_string(ctxt)
                );
                pcg_validity_assert!(
                    removed_cap >= collapse.capability,
                    [ctxt],
                    "Expected removed cap {:?} for {} to be at least {:?}",
                    removed_cap,
                    place.to_short_string(ctxt),
                    collapse.capability
                );
                let joined_cap = removed_cap.minimum(acc);
                pcg_validity_expect_some!(
                    joined_cap,
                    fallback: CapabilityKind::Exclusive,
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
