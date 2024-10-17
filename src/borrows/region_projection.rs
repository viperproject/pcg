use std::backtrace;

use crate::rustc_interface::{data_structures::fx::FxHashSet, middle::ty::RegionVid};

use crate::utils::{Place, PlaceRepacker};

use super::has_pcs_elem::HasPcsElems;
use super::{domain::MaybeOldPlace, latest::Latest};

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy)]
pub struct RegionProjection<'tcx> {
    pub place: MaybeOldPlace<'tcx>,
    region: RegionVid,
}

impl<'tcx> RegionProjection<'tcx> {
    pub fn new(region: RegionVid, place: MaybeOldPlace<'tcx>) -> Self {
        Self { place, region }
    }

    pub fn make_place_old(&mut self, place: Place<'tcx>, latest: &Latest<'tcx>) {
        self.place.make_place_old(place, latest);
    }

    pub fn index(&self, repacker: PlaceRepacker<'_, 'tcx>) -> usize {
        self.place
            .place()
            .projection_index(self.region, repacker)
            .unwrap()
    }

    pub fn region(&self) -> RegionVid {
        self.region
    }

    pub fn connections_between_places(
        source: MaybeOldPlace<'tcx>,
        dest: MaybeOldPlace<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> FxHashSet<(RegionProjection<'tcx>, RegionProjection<'tcx>)> {
        let mut edges = FxHashSet::default();
        for rp in source.region_projections(repacker) {
            for erp in dest.region_projections(repacker) {
                edges.insert((rp, erp));
            }
        }
        edges
    }
}

impl<'tcx> HasPcsElems<MaybeOldPlace<'tcx>> for RegionProjection<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        vec![&mut self.place]
    }
}
