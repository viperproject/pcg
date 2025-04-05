use super::latest::Latest;
use super::region_projection::RegionProjection;
use crate::utils::place::maybe_old::MaybeOldPlace;
use crate::utils::SnapshotLocation;
use crate::utils::{validity::HasValidityCheck, Place, CompilerCtxt};
use crate::validity_checks_enabled;

pub(crate) trait HasPcgElems<T> {
    fn pcg_elems(&mut self) -> Vec<&mut T>;
}

pub(crate) trait LabelRegionProjection<'tcx> {
    fn label_region_projection(
        &mut self,
        projection: &RegionProjection<'tcx, MaybeOldPlace<'tcx>>,
        location: SnapshotLocation,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> bool;
}

pub(crate) trait MakePlaceOld<'tcx> {
    fn make_place_old(
        &mut self,
        place: Place<'tcx>,
        latest: &Latest<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> bool;
}

pub(crate) fn default_make_place_old<
    'tcx,
    T: HasPcgElems<MaybeOldPlace<'tcx>> + HasValidityCheck<'tcx>,
>(
    this: &mut T,
    place: Place<'tcx>,
    latest: &Latest<'tcx>,
    repacker: CompilerCtxt<'_, 'tcx>,
) -> bool {
    let mut changed = false;
    for p in this.pcg_elems() {
        if p.make_place_old(place, latest) {
            changed = true;
        }
    }
    if validity_checks_enabled() {
        this.assert_validity(repacker);
    }
    changed
}
