use serde_json::json;

use super::{validity::HasValidityCheck, Place, PlaceRepacker};
use crate::utils::json::ToJsonWithRepacker;
use crate::{
    borrow_pcg::{borrow_pcg_edge::LocalNode, has_pcs_elem::HasPcsElems},
    combined_pcs::LocalNodeLike,
    rustc_interface::middle::mir::{BasicBlock, Location},
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

    pub(crate) fn to_json(&self) -> serde_json::Value {
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

impl<'tcx> LocalNodeLike<'tcx> for PlaceSnapshot<'tcx> {
    fn to_local_node(self) -> LocalNode<'tcx> {
        LocalNode::Place(self.into())
    }
}

impl<'tcx> HasValidityCheck<'tcx> for PlaceSnapshot<'tcx> {
    fn check_validity(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Result<(), String> {
        self.place.check_validity(repacker)
    }
}

impl<'tcx> std::fmt::Display for PlaceSnapshot<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} at {:?}", self.place, self.at)
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

impl<'tcx> HasPcsElems<Place<'tcx>> for PlaceSnapshot<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut Place<'tcx>> {
        vec![&mut self.place]
    }
}
