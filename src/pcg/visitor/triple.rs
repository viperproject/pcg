use crate::{
    free_pcs::{CapabilityKind, CapabilityLocal, LocalExpansions},
    pcg::{
        PcgError, PcgUnsupportedError,
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
                    CapabilityLocal::Allocated(LocalExpansions::new(local));
                self.pcg
                    .capabilities
                    .insert(local.into(), CapabilityKind::Write, self.ctxt);
            }
            PlaceCondition::Unalloc(_) | PlaceCondition::Return => {}
            PlaceCondition::RemoveCapability(_) => unreachable!(),
        }
        Ok(())
    }

    pub(crate) fn ensure_triple(&mut self, triple: Triple<'tcx>) -> Result<(), PcgError> {
        self.pcg.owned_ensures(triple, self.ctxt);
        Ok(())
    }
}
