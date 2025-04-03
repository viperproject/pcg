use serde_json::json;

use super::display::DisplayWithRepacker;
use super::{validity::HasValidityCheck, Place, PlaceRepacker};
use crate::borrow_pcg::region_projection::{
    MaybeRemoteRegionProjectionBase, PCGRegion, RegionIdx, RegionProjectionBaseLike,
};
use crate::pcg::{PCGNode, PCGNodeLike};
use crate::utils::json::ToJsonWithRepacker;
use crate::{
    borrow_pcg::{borrow_pcg_edge::LocalNode, has_pcs_elem::HasPcgElems},
    pcg::LocalNodeLike,
    rustc_interface::{
        index::IndexVec,
        middle::mir::{BasicBlock, Location},
    },
};

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy, Ord, PartialOrd)]
pub enum SnapshotLocation {
    After(Location),
    Start(BasicBlock),
}

impl SnapshotLocation {
    pub(crate) fn start() -> Self {
        SnapshotLocation::After(Location::START)
    }

    pub(crate) fn before(mut loc: Location) -> Self {
        if loc.statement_index == 0 {
            SnapshotLocation::Start(loc.block)
        } else {
            loc.statement_index -= 1;
            SnapshotLocation::After(loc)
        }
    }

    pub(crate) fn to_json(self) -> serde_json::Value {
        match self {
            SnapshotLocation::After(loc) => format!("after {:?}", loc).into(),
            SnapshotLocation::Start(bb) => format!("start {:?}", bb).into(),
        }
    }
}

impl From<Location> for SnapshotLocation {
    fn from(loc: Location) -> Self {
        SnapshotLocation::After(loc)
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy, Ord, PartialOrd)]
pub struct PlaceSnapshot<'tcx> {
    pub place: Place<'tcx>,
    pub at: SnapshotLocation,
}

impl<'tcx> RegionProjectionBaseLike<'tcx> for PlaceSnapshot<'tcx> {
    fn regions(&self, repacker: PlaceRepacker<'_, 'tcx>) -> IndexVec<RegionIdx, PCGRegion> {
        self.place.regions(repacker)
    }

    fn to_maybe_remote_region_projection_base(&self) -> MaybeRemoteRegionProjectionBase<'tcx> {
        MaybeRemoteRegionProjectionBase::Place((*self).into())
    }
}

impl<'tcx> PCGNodeLike<'tcx> for PlaceSnapshot<'tcx> {
    fn to_pcg_node(self, repacker: PlaceRepacker<'_, 'tcx>) -> PCGNode<'tcx> {
        self.to_local_node(repacker).into()
    }
}

impl<'tcx> LocalNodeLike<'tcx> for PlaceSnapshot<'tcx> {
    fn to_local_node(self, _repacker: PlaceRepacker<'_, 'tcx>) -> LocalNode<'tcx> {
        LocalNode::Place(self.into())
    }
}

impl<'tcx> HasValidityCheck<'tcx> for PlaceSnapshot<'tcx> {
    fn check_validity(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Result<(), String> {
        self.place.check_validity(repacker)
    }
}

impl std::fmt::Display for PlaceSnapshot<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} at {:?}", self.place, self.at)
    }
}

impl<'tcx> DisplayWithRepacker<'tcx> for PlaceSnapshot<'tcx> {
    fn to_short_string(&self, repacker: PlaceRepacker<'_, 'tcx>) -> String {
        format!("{} at {:?}", self.place.to_short_string(repacker), self.at)
    }
}

impl<'tcx> ToJsonWithRepacker<'tcx> for PlaceSnapshot<'tcx> {
    fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        json!({
            "place": self.place.to_json(repacker),
            "at": self.at.to_json(),
        })
    }
}

impl<'tcx> PlaceSnapshot<'tcx> {
    pub fn new<T: Into<SnapshotLocation>>(place: Place<'tcx>, at: T) -> Self {
        PlaceSnapshot {
            place,
            at: at.into(),
        }
    }

    pub(crate) fn with_inherent_region(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> PlaceSnapshot<'tcx> {
        PlaceSnapshot {
            place: self.place.with_inherent_region(repacker),
            at: self.at,
        }
    }
}

impl<'tcx> HasPcgElems<Place<'tcx>> for PlaceSnapshot<'tcx> {
    fn pcg_elems(&mut self) -> Vec<&mut Place<'tcx>> {
        vec![&mut self.place]
    }
}
