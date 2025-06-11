use super::latest::Latest;
use super::region_projection::{RegionProjection, RegionProjectionLabel};
use crate::borrow_pcg::edge_data::LabelPlacePredicate;
use crate::utils::place::maybe_old::MaybeOldPlace;
use crate::utils::CompilerCtxt;

pub(crate) trait HasPcgElems<T> {
    fn pcg_elems(&mut self) -> Vec<&mut T>;
}

pub(crate) trait LabelRegionProjection<'tcx> {
    #[allow(unused)]
    fn remove_rp_label(&mut self, place: MaybeOldPlace<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) -> bool;
    fn label_region_projection(
        &mut self,
        projection: &RegionProjection<'tcx, MaybeOldPlace<'tcx>>,
        label: Option<RegionProjectionLabel>,
        ctxt: CompilerCtxt<'_, 'tcx>,
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
