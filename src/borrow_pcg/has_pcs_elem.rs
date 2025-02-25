use super::latest::Latest;
use crate::utils::place::maybe_old::MaybeOldPlace;
use crate::utils::{validity::HasValidityCheck, Place, PlaceRepacker};
use crate::validity_checks_enabled;

pub(crate) trait HasPcsElems<T> {
    fn pcs_elems(&mut self) -> Vec<&mut T>;
}

pub(crate) trait MakePlaceOld<'tcx> {
    fn make_place_old(
        &mut self,
        place: Place<'tcx>,
        latest: &Latest<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool;
}

impl<'tcx, T> MakePlaceOld<'tcx> for T
where
    T: HasPcsElems<MaybeOldPlace<'tcx>> + HasValidityCheck<'tcx>,
{
    fn make_place_old(
        &mut self,
        place: Place<'tcx>,
        latest: &Latest<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        let mut changed = false;
        for p in self.pcs_elems() {
            if p.make_place_old(place, latest) {
                changed = true;
            }
        }
        if validity_checks_enabled() {
            self.assert_validity(repacker);
        }
        changed
    }
}
