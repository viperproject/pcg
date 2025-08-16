use crate::{
    error::{PcgError, PcgUnsupportedError},
    owned_pcg::{LocalExpansions, OwnedPcgLocal},
    pcg::{
        CapabilityKind,
        obtain::ObtainType,
        place_capabilities::PlaceCapabilitiesInterface,
        triple::{PlaceCondition, Triple},
    },
    utils::DataflowCtxt,
};

use super::PcgVisitor;

impl<'a, 'tcx: 'a, Ctxt: DataflowCtxt<'a, 'tcx>> PcgVisitor<'_, 'a, 'tcx, Ctxt> {
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
                self.pcg.owned[local] = OwnedPcgLocal::Allocated(LocalExpansions::new(local));
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
