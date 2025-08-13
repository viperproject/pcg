use crate::{
    owned_pcg::{LocalExpansions, OwnedPcgLocal},
    pcg::{
        CapabilityKind, PcgError, PcgUnsupportedError,
        obtain::ObtainType,
        place_capabilities::PlaceCapabilitiesInterface,
        triple::{PlaceCondition, Triple},
    },
};

use super::PcgVisitor;

impl<'tcx> PcgVisitor<'_, '_, 'tcx> {
    #[tracing::instrument(skip(self))]
    pub(crate) fn require_triple(&mut self, triple: Triple<'tcx>) -> Result<(), PcgError> {
        match triple.pre() {
            PlaceCondition::ExpandTwoPhase(place) => {
                if place.contains_unsafe_deref(self.ctxt) {
                    return Err(PcgError::unsupported(PcgUnsupportedError::DerefUnsafePtr));
                }
                self.place_obtainer()
                    .obtain(place, ObtainType::TwoPhaseExpand)?;
            }
            PlaceCondition::Capability(place, capability) => {
                if place.contains_unsafe_deref(self.ctxt) {
                    return Err(PcgError::unsupported(PcgUnsupportedError::DerefUnsafePtr));
                }
                self.place_obtainer()
                    .obtain(place, ObtainType::Capability(capability))?;
            }
            PlaceCondition::AllocateOrDeallocate(local) => {
                self.pcg.owned.locals_mut()[local] =
                    OwnedPcgLocal::Allocated(LocalExpansions::new(local));
                self.pcg
                    .capabilities
                    .insert(local.into(), CapabilityKind::Write, self.ctxt);
            }
            PlaceCondition::Unalloc(_) | PlaceCondition::Return => {}
            PlaceCondition::RemoveCapability(_) => unreachable!(),
        }
        Ok(())
    }

    #[tracing::instrument(skip(self, triple))]
    pub(crate) fn ensure_triple(&mut self, triple: Triple<'tcx>) -> Result<(), PcgError> {
        self.pcg.ensure_triple(triple, self.ctxt);
        Ok(())
    }
}
