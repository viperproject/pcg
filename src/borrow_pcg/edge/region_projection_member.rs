use crate::{
    borrow_pcg::{
        borrow_pcg_edge::LocalNode, edge_data::EdgeData, has_pcs_elem::{default_make_place_old, HasPcgElems, LabelRegionProjection, MakePlaceOld}, latest::Latest, region_projection::RegionProjection
    },
    pcg::{PCGNode, PCGNodeLike},
    rustc_interface::data_structures::fx::FxHashSet,
    utils::{
        display::DisplayWithRepacker, maybe_old::MaybeOldPlace, maybe_remote::MaybeRemotePlace, validity::HasValidityCheck, Place, PlaceRepacker, SnapshotLocation
    },
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum RpMemberDirection {
    PlaceOutlivesRegion,
    #[allow(dead_code)]
    RegionOutlivesPlace,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RegionProjectionMember<'tcx> {
    region_projection: RegionProjection<'tcx>,
    place: MaybeRemotePlace<'tcx>,
    direction: RpMemberDirection,
}

impl<'tcx> LabelRegionProjection<'tcx> for RegionProjectionMember<'tcx> {
    fn label_region_projection(
        &mut self,
        _projection: &RegionProjection<'tcx, MaybeOldPlace<'tcx>>,
        _location: SnapshotLocation,
        _repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        todo!()
    }
}

impl<'tcx> MakePlaceOld<'tcx> for RegionProjectionMember<'tcx> {
    fn make_place_old(
        &mut self,
        place: Place<'tcx>,
        latest: &Latest<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        default_make_place_old(self, place, latest, repacker)
    }
}

impl<'tcx> HasPcgElems<MaybeOldPlace<'tcx>> for RegionProjectionMember<'tcx> {
    fn pcg_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        let mut elems = self.region_projection.pcg_elems();
        elems.extend(self.place.pcg_elems());
        elems
    }
}

impl<'tcx> HasValidityCheck<'tcx> for RegionProjectionMember<'tcx> {
    fn check_validity(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Result<(), String> {
        self.region_projection.check_validity(repacker)?;
        self.place.check_validity(repacker)
    }
}

impl<'tcx> DisplayWithRepacker<'tcx> for RegionProjectionMember<'tcx> {
    fn to_short_string(&self, repacker: PlaceRepacker<'_, 'tcx>) -> String {
        format!(
            "{} -> {}",
            self.region_projection.to_short_string(repacker),
            self.place.to_short_string(repacker)
        )
    }
}

impl<'tcx> RegionProjectionMember<'tcx> {
    pub(crate) fn new(
        region_projection: RegionProjection<'tcx>,
        place: MaybeRemotePlace<'tcx>,
        direction: RpMemberDirection,
    ) -> Self {
        Self {
            region_projection,
            place,
            direction,
        }
    }

    pub(crate) fn blocked_node(&self) -> PCGNode<'tcx> {
        match self.direction {
            RpMemberDirection::PlaceOutlivesRegion => self.place.into(),
            RpMemberDirection::RegionOutlivesPlace => self.region_projection.into(),
        }
    }

    pub(crate) fn blocked_by_node(&self, repacker: PlaceRepacker<'_, 'tcx>) -> LocalNode<'tcx> {
        match self.direction {
            RpMemberDirection::PlaceOutlivesRegion => {
                self.region_projection.try_to_local_node(repacker).unwrap()
            }
            RpMemberDirection::RegionOutlivesPlace => {
                self.place.try_to_local_node(repacker).unwrap()
            }
        }
    }

    pub(crate) fn direction(&self) -> RpMemberDirection {
        self.direction
    }
}

impl<'tcx> EdgeData<'tcx> for RegionProjectionMember<'tcx> {
    fn blocked_nodes(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<PCGNode<'tcx>> {
        std::iter::once(self.blocked_node()).collect()
    }

    fn blocked_by_nodes(&self, repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<LocalNode<'tcx>> {
        std::iter::once(self.blocked_by_node(repacker)).collect()
    }
}
