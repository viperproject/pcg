use crate::rustc_interface::middle::mir::{BasicBlock, Location};

use super::{Place, PlaceRepacker};

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy)]
pub enum SnapshotLocation {
    Location(Location),
    Join(BasicBlock),
}

impl From<Location> for SnapshotLocation {
    fn from(loc: Location) -> Self {
        SnapshotLocation::Location(loc)
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy)]
pub struct PlaceSnapshot<'tcx> {
    pub place: Place<'tcx>,
    pub at: SnapshotLocation,
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
