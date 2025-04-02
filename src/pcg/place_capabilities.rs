use itertools::Itertools;

use crate::{
    free_pcs::CapabilityKind,
    rustc_interface::{data_structures::fx::FxHashMap, middle::mir},
    utils::{
        display::{DebugLines, DisplayWithRepacker},
        maybe_old::MaybeOldPlace,
        Place, PlaceRepacker,
    },
};

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct PlaceCapabilities<'tcx>(pub(crate) FxHashMap<MaybeOldPlace<'tcx>, CapabilityKind>);

impl<'tcx> DebugLines<PlaceRepacker<'_, 'tcx>> for PlaceCapabilities<'tcx> {
    fn debug_lines(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Vec<String> {
        self.iter()
            .map(|(node, capability)| {
                format!("{}: {:?}", node.to_short_string(repacker), capability)
            })
            .sorted()
            .collect()
    }
}

impl<'tcx> PlaceCapabilities<'tcx> {
    pub(crate) fn get_longest_prefix(&self, to: Place<'tcx>) -> Place<'tcx> {
        self.iter()
            .flat_map(|(p, _)| p.try_into())
            .filter(|p: &Place| p.is_prefix(to))
            .max_by_key(|p| p.projection.len())
            .unwrap_or(to.local.into())
    }

    pub(crate) fn owned_capabilities<'mir: 'slf, 'slf>(
        &'slf mut self,
        local: mir::Local,
        repacker: PlaceRepacker<'mir, 'tcx>,
    ) -> impl Iterator<Item = (MaybeOldPlace<'tcx>, &'slf mut CapabilityKind)> + 'slf {
        self.0.iter_mut().filter_map(move |(place, capability)| {
            if place.local() == local && place.is_owned(repacker) {
                Some((*place, capability))
            } else {
                None
            }
        })
    }

    pub(crate) fn rename_place(
        &mut self,
        old: MaybeOldPlace<'tcx>,
        new: MaybeOldPlace<'tcx>,
    ) -> bool {
        let mut changed = false;
        self.0 = self
            .0
            .clone()
            .into_iter()
            .map(|(mut place, capability)| {
                if place == old {
                    place = new;
                    changed = true;
                }
                (place, capability)
            })
            .collect();
        changed
    }

    /// Returns true iff the capability was changed.
    pub(crate) fn insert(
        &mut self,
        place: MaybeOldPlace<'tcx>,
        capability: CapabilityKind,
    ) -> bool {
        self.0.insert(place, capability) != Some(capability)
    }

    pub(crate) fn remove(&mut self, place: MaybeOldPlace<'tcx>) -> Option<CapabilityKind> {
        self.0.remove(&place)
    }

    pub fn iter(&self) -> impl Iterator<Item = (MaybeOldPlace<'tcx>, CapabilityKind)> + '_ {
        self.0.iter().map(|(k, v)| (*k, *v))
    }

    pub(crate) fn get(&self, place: MaybeOldPlace<'tcx>) -> Option<CapabilityKind> {
        self.0.get(&place).copied()
    }

    pub(crate) fn join(&mut self, other: &Self) -> bool {
        let mut changed = false;
        for (place, other_capability) in other.iter() {
            match self.0.get(&place) {
                Some(self_capability) => {
                    if let Some(c) = self_capability.minimum(other_capability) {
                        changed |= self.0.insert(place, c) != Some(c);
                    } else {
                        self.0.remove(&place);
                        changed = true;
                    }
                }
                None => {
                    self.0.insert(place, other_capability);
                    changed = true;
                }
            }
        }
        changed
    }
}
