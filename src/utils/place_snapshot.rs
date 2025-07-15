use serde_json::json;

use super::display::DisplayWithCompilerCtxt;
use super::{validity::HasValidityCheck, CompilerCtxt, Place};
use crate::borrow_pcg::region_projection::{
    MaybeRemoteRegionProjectionBase, PcgRegion, RegionIdx, RegionProjectionBaseLike,
};
use crate::pcg::{PCGNode, PCGNodeLike};
use crate::utils::json::ToJsonWithCompilerCtxt;
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
    Start(BasicBlock),
    Prepare(Location),
    BeforeCollapse(Location),
    Mid(Location),
    After(Location),
    Loop(BasicBlock),
}

impl SnapshotLocation {
    pub(crate) fn location(self) -> Location {
        match self {
            SnapshotLocation::Prepare(location) => location,
            SnapshotLocation::BeforeCollapse(location) => location,
            SnapshotLocation::Mid(location) => location,
            SnapshotLocation::After(location) => location,
            SnapshotLocation::Start(basic_block) | SnapshotLocation::Loop(basic_block) => {
                Location {
                    block: basic_block,
                    statement_index: 0,
                }
            }
        }
    }
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
        self.to_string().into()
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy, Ord, PartialOrd)]
pub struct PlaceSnapshot<'tcx> {
    pub(crate) place: Place<'tcx>,
    pub(crate) at: SnapshotLocation,
}

impl std::fmt::Display for SnapshotLocation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SnapshotLocation::After(loc) => write!(f, "after {loc:?}"),
            SnapshotLocation::Mid(loc) => write!(f, "mid {loc:?}"),
            SnapshotLocation::Start(bb) => write!(f, "start {bb:?}"),
            SnapshotLocation::Loop(bb) => write!(f, "loop {bb:?}"),
            SnapshotLocation::Prepare(location) => write!(f, "prep {location:?}"),
            SnapshotLocation::BeforeCollapse(location) => write!(f, "before collapse {location:?}"),
        }
    }
}

impl<'tcx> RegionProjectionBaseLike<'tcx> for PlaceSnapshot<'tcx> {
    fn regions<C: Copy>(
        &self,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> IndexVec<RegionIdx, PcgRegion> {
        self.place.regions(repacker)
    }

    fn to_maybe_remote_region_projection_base(&self) -> MaybeRemoteRegionProjectionBase<'tcx> {
        MaybeRemoteRegionProjectionBase::Place((*self).into())
    }
}

impl<'tcx> PCGNodeLike<'tcx> for PlaceSnapshot<'tcx> {
    fn to_pcg_node<C: Copy>(self, repacker: CompilerCtxt<'_, 'tcx, C>) -> PCGNode<'tcx> {
        self.to_local_node(repacker).into()
    }
}

impl<'tcx> LocalNodeLike<'tcx> for PlaceSnapshot<'tcx> {
    fn to_local_node<C: Copy>(self, _repacker: CompilerCtxt<'_, 'tcx, C>) -> LocalNode<'tcx> {
        LocalNode::Place(self.into())
    }
}

impl<'tcx> HasValidityCheck<'tcx> for PlaceSnapshot<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        self.place.check_validity(ctxt)
    }
}

impl std::fmt::Display for PlaceSnapshot<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} at {:?}", self.place, self.at)
    }
}

impl<'tcx, BC: Copy> DisplayWithCompilerCtxt<'tcx, BC> for PlaceSnapshot<'tcx> {
    fn to_short_string(&self, repacker: CompilerCtxt<'_, 'tcx, BC>) -> String {
        format!("{} at {:?}", self.place.to_short_string(repacker), self.at)
    }
}

impl<'tcx, BC: Copy> ToJsonWithCompilerCtxt<'tcx, BC> for PlaceSnapshot<'tcx> {
    fn to_json(&self, repacker: CompilerCtxt<'_, 'tcx, BC>) -> serde_json::Value {
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

    pub fn place(&self) -> Place<'tcx> {
        self.place
    }

    pub fn at(&self) -> SnapshotLocation {
        self.at
    }

    pub(crate) fn with_inherent_region(
        &self,
        repacker: CompilerCtxt<'_, 'tcx>,
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
