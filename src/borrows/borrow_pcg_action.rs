use crate::combined_pcs::UnblockAction;
use crate::free_pcs::CapabilityKind;
use crate::rustc_interface::middle::mir::Location;
use crate::utils::{Place, PlaceRepacker};

use super::borrow_pcg_edge::BorrowPCGEdge;
use super::borrows_state::BorrowsState;
use super::borrows_visitor::BorrowsVisitor;
use super::path_condition::PathConditions;
use super::region_projection_member::RegionProjectionMember;

/// An action that is applied to a `BorrowsState` during the dataflow analysis
/// of `BorrowsVisitor`, for which consumers (e.g. Prusti) may wish to perform
/// their own effect (e.g. for an unblock, applying a magic wand).
///
/// N.B. Currently annotations for consumers are generated via the `bridge`
/// functionality which generates annotations between two arbitrary
/// `BorrowsState`s. Ultimately, we want to remove that functionality and
/// instead generate annotations for consumers directly in the `BorrowsVisitor`.
#[derive(Clone)]
pub(crate) enum BorrowPcgAction<'tcx> {
    MakePlaceOld(Place<'tcx>),
    SetLatest(Place<'tcx>, Location),
    Unblock(UnblockAction<'tcx>, Location),
    AddRegionProjectionMember(RegionProjectionMember<'tcx>, PathConditions),
}

impl<'tcx, 'mir, 'state> BorrowsVisitor<'tcx, 'mir, 'state> {
    pub(crate) fn apply_action(&mut self, action: BorrowPcgAction<'tcx>) {
        self.state
            .post_state_mut()
            .apply_action(action, self.repacker);
    }
}

impl<'tcx> BorrowsState<'tcx> {
    pub(crate) fn apply_action(&mut self, action: BorrowPcgAction<'tcx>, repacker: PlaceRepacker<'_, 'tcx>) {
        match action {
            BorrowPcgAction::MakePlaceOld(place) => {
                self.make_place_old(place, repacker, None);
            }
            BorrowPcgAction::SetLatest(place, location) => {
                self.set_latest(place, location, repacker);
            }
            BorrowPcgAction::Unblock(unblock_action, location) => {
                self.apply_unblock_action(unblock_action, repacker, location);
            }
            BorrowPcgAction::AddRegionProjectionMember(member, pc) => {
                self.add_region_projection_member(member, pc, repacker);
            }
        }
    }
}
