use crate::rustc_interface::middle::mir::Location;
use crate::utils::PlaceRepacker;

use super::{
    domain::{MaybeOldPlace, MaybeRemotePlace},
    has_pcs_elem::HasPcsElems,
    region_projection::RegionProjection,
};
#[derive(Clone, Debug, Hash, PartialEq, Eq, Copy)]
pub enum RegionProjectionMemberDirection {
    PlaceIsRegionInput,
    PlaceIsRegionOutput,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct RegionProjectionMember<'tcx> {
    pub place: MaybeRemotePlace<'tcx>,
    pub projection: RegionProjection<'tcx>,
    location: Location,
    pub direction: RegionProjectionMemberDirection,
}

impl<'tcx> HasPcsElems<RegionProjection<'tcx>> for RegionProjectionMember<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut RegionProjection<'tcx>> {
        vec![&mut self.projection]
    }
}

impl<'tcx> HasPcsElems<MaybeOldPlace<'tcx>> for RegionProjectionMember<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        let mut vec = self.place.pcs_elems();
        vec.extend(self.projection.pcs_elems());
        vec
    }
}

impl<'tcx> RegionProjectionMember<'tcx> {

    pub fn projection_index(&self, repacker: PlaceRepacker<'_, 'tcx>) -> usize {
        self.projection.index(repacker)
    }

    pub fn location(&self) -> Location {
        self.location
    }

    pub fn new(
        place: MaybeRemotePlace<'tcx>,
        projection: RegionProjection<'tcx>,
        location: Location,
        direction: RegionProjectionMemberDirection,
    ) -> Self {
        Self {
            place,
            projection,
            location,
            direction,
        }
    }
}
