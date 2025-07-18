use itertools::Itertools;

use crate::{
    borrow_pcg::borrow_pcg_expansion::BorrowPcgExpansion,
    free_pcs::CapabilityKind,
    pcg::PcgError,
    pcg_validity_assert,
    rustc_interface::{data_structures::fx::FxHashMap, middle::mir},
    utils::{
        display::{DebugLines, DisplayWithCompilerCtxt},
        validity::HasValidityCheck,
        CompilerCtxt, HasPlace, Place,
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
    fn remove(
        &mut self,
        place: Place<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Option<CapabilityKind>;
}

impl<'tcx> PlaceCapabilitiesInterface<'tcx> for PlaceCapabilities<'tcx> {
    fn get(&self, place: Place<'tcx>) -> Option<CapabilityKind> {
        self.0.get(&place).copied()
    }

    fn remove(
        &mut self,
        place: Place<'tcx>,
        _ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Option<CapabilityKind> {
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

#[derive(Clone, Copy)]
pub(crate) enum BlockType {
    DerefExclusive,
    Read,
    Other,
}

impl BlockType {
    pub(crate) fn blocked_place_retained_capability(self) -> Option<CapabilityKind> {
        match self {
            BlockType::DerefExclusive => Some(CapabilityKind::ShallowExclusive),
            BlockType::Read => Some(CapabilityKind::Read),
            BlockType::Other => None
        }
    }
    pub(crate) fn expansion_capability<'tcx>(
        self,
        _blocked_place: Place<'tcx>,
        blocked_capability: CapabilityKind,
        _ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> CapabilityKind {
        match self {
            BlockType::DerefExclusive => CapabilityKind::Exclusive,
            BlockType::Read => CapabilityKind::Read,
            BlockType::Other => blocked_capability,
        }
    }
}

impl<'tcx> PlaceCapabilities<'tcx> {
    pub(crate) fn update_for_expansion(
        &mut self,
        expansion: &BorrowPcgExpansion<'tcx>,
        block_type: BlockType,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<bool, PcgError> {
        let mut changed = false;
        // We dont change if only expanding region projections
        if expansion.base.is_place() {
            let base = expansion.base;
            let base_capability = self.get(base.place());
            let expanded_capability = if let Some(capability) = base_capability {
                block_type.expansion_capability(base.place(), capability, ctxt)
            } else {
                // TODO
                // pcg_validity_assert!(
                //     false,
                //     "Base capability for {} is not set",
                //     base.place().to_short_string(ctxt)
                // );
                return Ok(true);
                // panic!("Base capability should be set");
            };

            changed |= self.update_capabilities_for_block_of_place(base.place(), block_type, ctxt);

            for p in expansion.expansion.iter() {
                changed |= self.insert(p.place(), expanded_capability, ctxt);
            }
        }
        Ok(changed)
    }
    pub(crate) fn update_capabilities_for_block_of_place(
        &mut self,
        blocked_place: Place<'tcx>,
        block_type: BlockType,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        let retained_capability = block_type.blocked_place_retained_capability();
        if let Some(capability) = retained_capability {
            self.insert(blocked_place, capability, ctxt)
        } else {
            self.remove(blocked_place, ctxt).is_some()
        }
    }

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
