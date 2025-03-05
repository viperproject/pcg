use crate::{
    borrow_pcg::{
        borrow_pcg_edge::LocalNode, edge_data::EdgeData, has_pcs_elem::HasPcgElems, region_projection::RegionProjection
    },
    combined_pcs::{PCGNode, PCGNodeLike},
    rustc_interface::data_structures::fx::FxHashSet,
    utils::{
        display::DisplayWithRepacker, maybe_old::MaybeOldPlace, maybe_remote::MaybeRemotePlace,
        validity::HasValidityCheck, PlaceRepacker,
    },
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum RpMemberDirection {
    PlaceOutlivesRegion,
    RegionOutlivesPlace,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RegionProjectionMember<'tcx> {
    region_projection: RegionProjection<'tcx>,
    place: MaybeRemotePlace<'tcx>,
    direction: RpMemberDirection,
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
}

impl<'tcx> EdgeData<'tcx> for RegionProjectionMember<'tcx> {
    fn blocked_nodes(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<PCGNode<'tcx>> {
        std::iter::once(self.blocked_node()).collect()
    }

    fn blocked_by_nodes(&self, repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<LocalNode<'tcx>> {
        std::iter::once(self.blocked_by_node(repacker)).collect()
    }
}
