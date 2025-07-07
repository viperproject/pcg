use crate::{
    free_pcs::{CapabilityKind, CapabilityLocal, CapabilityProjections},
    pcg::{
        obtain::ObtainType, triple::{PlaceCondition, Triple}, PcgError, PcgUnsupportedError
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
                self.obtain(place, ObtainType::TwoPhaseExpand)?;
            }
            PlaceCondition::Capability(place, capability) => {
                if place.contains_unsafe_deref(self.ctxt) {
                    return Err(PcgError::unsupported(PcgUnsupportedError::DerefUnsafePtr));
                }
                self.obtain(place, ObtainType::Capability(capability))?;
            }
            PlaceCondition::RemoveCapability(place) => {
                self.pcg.capabilities.remove(place);
            }
            PlaceCondition::AllocateOrDeallocate(local) => {
                self.pcg.owned.locals_mut()[local] =
                    CapabilityLocal::Allocated(CapabilityProjections::new(local));
                self.pcg
                    .capabilities
                    .insert(local.into(), CapabilityKind::Write);
            }
            PlaceCondition::Unalloc(_) | PlaceCondition::Return => {}
        }
        Ok(())
    }

    pub(crate) fn ensure_triple(&mut self, triple: Triple<'tcx>) -> Result<(), PcgError> {
        self.pcg.owned_ensures(triple);
        Ok(())
    }
}
