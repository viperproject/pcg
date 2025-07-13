use derive_more::From;

use super::latest::Latest;
use super::region_projection::{RegionProjection, RegionProjectionLabel};
use crate::borrow_pcg::edge_data::LabelPlacePredicate;
use crate::borrow_pcg::region_projection::RegionIdx;
use crate::utils::place::maybe_old::MaybeOldPlace;
use crate::utils::CompilerCtxt;

pub(crate) trait HasPcgElems<T> {
    fn pcg_elems(&mut self) -> Vec<&mut T>;
}

#[derive(From, PartialEq, Eq, Hash, Debug)]
pub(crate) enum LabelRegionProjectionPredicate<'tcx> {
    Equals(RegionProjection<'tcx, MaybeOldPlace<'tcx>>),
    AllNonPlaceHolder(MaybeOldPlace<'tcx>, RegionIdx),
}

impl<'tcx> LabelRegionProjectionPredicate<'tcx> {
    pub(crate) fn matches(
        &self,
        region_projection: RegionProjection<'tcx, MaybeOldPlace<'tcx>>,
    ) -> bool {
        match self {
            LabelRegionProjectionPredicate::Equals(projection) => *projection == region_projection,
            LabelRegionProjectionPredicate::AllNonPlaceHolder(maybe_old_place, region_idx) => {
                region_projection.region_idx == *region_idx
                    && region_projection.place() == *maybe_old_place
                    && !region_projection.is_placeholder()
            }
        }
    }
}

pub(crate) trait LabelRegionProjection<'tcx> {
    fn label_region_projection(
        &mut self,
        predicate: &LabelRegionProjectionPredicate<'tcx>,
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
