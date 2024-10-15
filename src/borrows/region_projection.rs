use crate::rustc_interface::{data_structures::fx::FxHashSet, middle::ty::RegionVid};

use crate::utils::{Place, PlaceRepacker};

use super::{domain::MaybeOldPlace, latest::Latest};

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy)]
pub struct RegionProjection<'tcx> {
    pub place: MaybeOldPlace<'tcx>,
    pub region: RegionVid,
}

impl<'tcx> RegionProjection<'tcx> {
    pub fn new(region: RegionVid, place: MaybeOldPlace<'tcx>) -> Self {
        Self { place, region }
    }
    pub fn make_place_old(&mut self, place: Place<'tcx>, latest: &Latest) {
        self.place.make_place_old(place, latest);
    }
    pub fn index(&self, repacker: PlaceRepacker<'_, 'tcx>) -> usize {
        self.place
            .place()
            .projection_index(self.region, repacker)
            .unwrap()
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

pub trait HasRegionProjections<'tcx> {
    fn region_projections(&mut self) -> Vec<&mut RegionProjection<'tcx>>;

    fn mut_region_projections(
        &mut self,
        mut f: impl FnMut(&mut RegionProjection<'tcx>) -> bool,
    ) -> bool {
        let mut changed = false;
        for p in self.region_projections() {
            if f(p) {
                changed = true;
            }
        }
        changed
    }
}
