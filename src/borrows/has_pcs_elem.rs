use crate::utils::Place;

use super::{domain::MaybeOldPlace, latest::Latest};

pub (crate) trait HasPcsElems<T> {
    fn pcs_elems(&mut self) -> Vec<&mut T>;

}

pub (crate) trait MakePlaceOld<'tcx> {
    fn make_place_old(&mut self, place: Place<'tcx>, latest: &Latest<'tcx>) -> bool;
}

impl<'tcx, T> MakePlaceOld<'tcx> for T
where
    T: HasPcsElems<MaybeOldPlace<'tcx>>,
{
    fn make_place_old(&mut self, place: Place<'tcx>, latest: &Latest<'tcx>) -> bool {
        let mut changed = false;
        for p in self.pcs_elems() {
            if p.make_place_old(place, latest) {
                changed = true;
            }
        }
        changed
    }
}

