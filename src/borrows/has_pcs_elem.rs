use crate::utils::Place;

use super::{domain::MaybeOldPlace, latest::Latest};

pub trait HasPcsElems<T> {
    fn pcs_elems(&mut self) -> Vec<&mut T>;

    fn mut_pcs_elems(&mut self, mut f: impl FnMut(&mut T) -> bool) -> bool {
        let mut changed = false;
        for p in self.pcs_elems() {
            if f(p) {
                changed = true;
            }
        }
        changed
    }

}

pub trait MakePlaceOld<'tcx> {
    fn make_place_old(&mut self, place: Place<'tcx>, latest: &Latest<'tcx>);
}

impl<'tcx, T> MakePlaceOld<'tcx> for T
where
    T: HasPcsElems<MaybeOldPlace<'tcx>>,
{
    fn make_place_old(&mut self, place: Place<'tcx>, latest: &Latest<'tcx>) {
        for p in self.pcs_elems() {
            p.make_place_old(place, latest);
        }
    }
}

