use crate::{
    free_pcs::{CapabilityKind, CapabilityLocal, CapabilityProjections},
    pcg::{
        triple::{PlaceCondition, Triple},
        PCGUnsupportedError, PcgError,
    },
    rustc_interface::middle::mir::Location,
};

use super::PcgVisitor;

impl<'pcg, 'mir, 'tcx> PcgVisitor<'pcg, 'mir, 'tcx> {
    #[tracing::instrument(skip(self, location))]
    pub(crate) fn require_triple(
        &mut self,
        triple: Triple<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        match triple.pre() {
            PlaceCondition::Capability(place, capability) => {
                if place.contains_unsafe_deref(self.ctxt) {
                    return Err(PcgError::unsupported(PCGUnsupportedError::DerefUnsafePtr));
                }
                self.obtain(place, location, capability)?;
            }
            PlaceCondition::RemoveCapability(place) => {
                self.pcg.capabilities.remove(place.into());
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
