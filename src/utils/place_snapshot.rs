use serde_json::json;

use crate::{
    borrows::{domain::ToJsonWithRepacker, has_pcs_elem::HasPcsElems},
    rustc_interface::middle::mir::{BasicBlock, Location},
};

use super::{Place, PlaceRepacker};

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy)]
pub enum SnapshotLocation {
    After(Location),
    Start(BasicBlock),
}

impl SnapshotLocation {
    pub (crate) fn start() -> Self {
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

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy)]
pub struct PlaceSnapshot<'tcx> {
    pub place: Place<'tcx>,
    pub at: SnapshotLocation,
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

    pub fn project_deref(&self, repacker: PlaceRepacker<'_, 'tcx>) -> PlaceSnapshot<'tcx> {
        PlaceSnapshot {
            place: self.place.project_deref(repacker),
            at: self.at,
        }
    }

    pub fn prefix_place(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Option<PlaceSnapshot<'tcx>> {
        self.place.prefix_place(repacker).map(|p| PlaceSnapshot {
            place: p,
            at: self.at,
        })
    }

    pub fn with_inherent_region(&self, repacker: PlaceRepacker<'_, 'tcx>) -> PlaceSnapshot<'tcx> {
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
