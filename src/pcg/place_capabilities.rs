use itertools::Itertools;

use crate::{
    free_pcs::CapabilityKind,
    pcg_validity_assert,
    rustc_interface::{data_structures::fx::FxHashMap, middle::mir},
    utils::{
        display::{DebugLines, DisplayWithCompilerCtxt},
        validity::HasValidityCheck,
        CompilerCtxt, Place,
    },
};

pub(crate) trait PlaceCapabilitiesInterface<'tcx> {
    fn get(&self, place: Place<'tcx>) -> Option<CapabilityKind>;
    fn insert(
        &mut self,
        place: Place<'tcx>,
        capability: CapabilityKind,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool;
    fn remove(&mut self, place: Place<'tcx>) -> Option<CapabilityKind>;
}

impl<'tcx> PlaceCapabilitiesInterface<'tcx> for PlaceCapabilities<'tcx> {
    fn get(&self, place: Place<'tcx>) -> Option<CapabilityKind> {
        self.0.get(&place).copied()
    }

    fn remove(&mut self, place: Place<'tcx>) -> Option<CapabilityKind> {
        self.0.remove(&place)
    }

    fn insert(
        &mut self,
        place: Place<'tcx>,
        capability: CapabilityKind,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        pcg_validity_assert!(
            !place.projects_shared_ref(ctxt) || capability.is_read(),
            "Place {} projects a shared ref, but has capability {:?}",
            place.to_short_string(ctxt),
            capability
        );
        self.0.insert(place, capability) != Some(capability)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct PlaceCapabilities<'tcx>(pub(crate) FxHashMap<Place<'tcx>, CapabilityKind>);

impl<'tcx> HasValidityCheck<'tcx> for PlaceCapabilities<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        for (place, cap) in self.iter() {
            if place.projects_shared_ref(ctxt) && !cap.is_read() {
                return Err(format!(
                    "Place {} projects a shared ref, but has capability {:?}",
                    place.to_short_string(ctxt),
                    cap
                ));
            }
        }
        Ok(())
    }
}

impl<'tcx> DebugLines<CompilerCtxt<'_, 'tcx>> for PlaceCapabilities<'tcx> {
    fn debug_lines(&self, repacker: CompilerCtxt<'_, 'tcx>) -> Vec<String> {
        self.iter()
            .map(|(node, capability)| {
                format!("{}: {:?}", node.to_short_string(repacker), capability)
            })
            .sorted()
            .collect()
    }
}

impl<'tcx> PlaceCapabilities<'tcx> {
    pub fn is_exclusive(&self, place: Place<'tcx>) -> bool {
        self.get(place)
            .map(|c| c == CapabilityKind::Exclusive)
            .unwrap_or(false)
    }

    pub(crate) fn owned_capabilities<'mir: 'slf, 'slf, 'bc: 'slf>(
        &'slf mut self,
        local: mir::Local,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> impl Iterator<Item = (Place<'tcx>, &'slf mut CapabilityKind)> + use<'tcx, 'slf, 'mir> {
        self.0.iter_mut().filter_map(move |(place, capability)| {
            if place.local == local && place.is_owned(ctxt) {
                Some((*place, capability))
            } else {
                None
            }
        })
    }

    pub fn iter(&self) -> impl Iterator<Item = (Place<'tcx>, CapabilityKind)> + '_ {
        self.0.iter().map(|(k, v)| (*k, *v))
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
                None => {}
            }
        }
        changed
    }
}
