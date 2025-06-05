use super::latest::Latest;
use super::region_projection::{RegionProjection, RegionProjectionLabel};
use crate::borrow_pcg::edge_data::LabelPlacePredicate;
use crate::utils::place::maybe_old::MaybeOldPlace;
use crate::utils::SnapshotLocation;
use crate::utils::{validity::HasValidityCheck, CompilerCtxt, Place};
use crate::validity_checks_enabled;

pub(crate) trait HasPcgElems<T> {
    fn pcg_elems(&mut self) -> Vec<&mut T>;
}

pub(crate) trait LabelRegionProjection<'tcx> {
    fn label_region_projection(
        &mut self,
        projection: &RegionProjection<'tcx, MaybeOldPlace<'tcx>>,
        label: Option<RegionProjectionLabel>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> bool;
}

pub(crate) trait LabelPlace<'tcx> {
    fn label_place(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        latest: &Latest<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool;
}

pub(crate) fn default_label_place<
    'tcx,
    T: HasPcgElems<MaybeOldPlace<'tcx>> + HasValidityCheck<'tcx>,
>(
    this: &mut T,
    predicate: &LabelPlacePredicate<'tcx>,
    latest: &Latest<'tcx>,
    ctxt: CompilerCtxt<'_, 'tcx>,
) -> bool {
    let mut changed = false;
    for p in this.pcg_elems() {
        if p.label_place(&predicate, latest, ctxt) {
            changed = true;
        }
    }
    if validity_checks_enabled() {
        this.assert_validity(ctxt);
    }
    changed
}
