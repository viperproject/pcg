use crate::borrow_pcg::action::BorrowPCGAction;
use crate::borrow_pcg::state::obtain::ObtainReason;
use crate::free_pcs::CapabilityKind;
use crate::pcg_validity_assert;
use crate::rustc_interface::middle::mir::Location;

use crate::utils::Place;

use super::{PcgError, PcgVisitor};
impl<'tcx> PcgVisitor<'_, '_, 'tcx> {
    pub(crate) fn upgrade_read_to_exclusive(&mut self, place: Place<'tcx>) -> Result<(), PcgError> {
        self.record_and_apply_action(
            BorrowPCGAction::restore_capability(place.into(), CapabilityKind::Exclusive).into(),
        )?;
        self.remove_read_permission_upwards(place)?;
        Ok(())
    }

    pub(crate) fn remove_read_permission_upwards(
        &mut self,
        mut current: Place<'tcx>,
    ) -> Result<(), PcgError> {
        while !current.is_owned(self.ctxt)
            && self.pcg.capabilities.get(current.into()) == Some(CapabilityKind::Read)
        {
            self.record_and_apply_action(
                BorrowPCGAction::weaken(current, CapabilityKind::Read, None).into(),
            )?;
            let parent = match current.parent_place() {
                Some(parent) => parent,
                None => break,
            };
            current = parent;
        }
        Ok(())
    }

    pub(crate) fn upgrade_closest_root_to_exclusive(
        &mut self,
        place: Place<'tcx>,
    ) -> Result<(), PcgError> {
        // It's possible that `place` is not in the PCG, `expand_root` is the leaf
        // node from which place will be expanded to.

        let mut expand_root = place;
        while self.pcg.capabilities.get(expand_root.into()).is_none() {
            if expand_root.is_owned(self.ctxt) {
                return Ok(());
            }
            expand_root = expand_root.parent_place().unwrap();
        }

        // The expand_root may have capability read only. We upgrade it to
        // Exclusive, then we change all Read permissions from `expand_root`'s
        // parents to be None instead to ensure they are no longer accessible.

        if !expand_root.is_owned(self.ctxt)
            && self.pcg.capabilities.get(expand_root.into()) == Some(CapabilityKind::Read)
        {
            self.upgrade_read_to_exclusive(expand_root)
        } else {
            Ok(())
        }
    }

    /// Ensures that the place is expanded to the given place, with a certain
    /// capability.
    ///
    /// This also handles corresponding region projections of the place.
    pub(crate) fn obtain(
        &mut self,
        place: Place<'tcx>,
        location: Location,
        obtain_reason: ObtainReason,
    ) -> Result<(), PcgError> {
        if obtain_reason.min_post_obtain_capability() != CapabilityKind::Read {
            self.upgrade_closest_root_to_exclusive(place)?;
        }

        if !self.pcg.borrow.contains(place, self.ctxt) {
            let actions = self.pcg.borrow.expand_to(
                place,
                &mut self.pcg.capabilities,
                self.ctxt,
                obtain_reason,
                location,
            )?;
            self.record_actions(actions);
        }
        if !place.is_owned(self.ctxt) {
            pcg_validity_assert!(
                self.pcg.capabilities.get(place.into()).is_some(),
                "{:?}: Place {:?} does not have a capability after obtain {:?}",
                location,
                place,
                obtain_reason
            );
            pcg_validity_assert!(
                self.pcg.capabilities.get(place.into()).unwrap()
                    >= obtain_reason.min_post_obtain_capability(),
                "{:?} Capability {:?} for {:?} is not greater than {:?}",
                location,
                self.pcg.capabilities.get(place.into()).unwrap(),
                place,
                obtain_reason.min_post_obtain_capability()
            );
        }
        Ok(())
    }
}
