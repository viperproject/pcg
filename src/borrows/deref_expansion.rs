use serde_json::json;

use crate::{
    rustc_interface::{
        data_structures::fx::FxHashSet,
        middle::mir::{Location, PlaceElem},
    },
    utils::PlaceRepacker,
};

use super::{
    borrow_pcg_edge::{BlockedNode, BlockingNode},
    domain::{MaybeOldPlace, ToJsonWithRepacker},
    has_pcs_elem::HasPcsElems,
    region_projection::RegionProjection,
};

/// An expansion of a place in the PCS
#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct DerefExpansion<'tcx> {
    base: MaybeOldPlace<'tcx>,
    expansion: Vec<PlaceElem<'tcx>>,
    pub location: Location,
}

impl<'tcx> DerefExpansion<'tcx> {
    pub fn new(
        base: MaybeOldPlace<'tcx>,
        expansion: Vec<PlaceElem<'tcx>>,
        location: Location,
    ) -> Self {
        Self {
            base,
            expansion,
            location,
        }
    }

    pub fn base(&self) -> MaybeOldPlace<'tcx> {
        self.base
    }

    pub fn expansion(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Vec<MaybeOldPlace<'tcx>> {
        self.expansion
            .iter()
            .map(|p| self.base.project_deeper(repacker.tcx(), *p))
            .collect()
    }

    pub fn blocked_nodes(&self) -> FxHashSet<BlockedNode<'tcx>> {
        vec![self.base.into()].into_iter().collect()
    }

    pub fn blocked_by_nodes(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> FxHashSet<BlockingNode<'tcx>> {
        self.expansion(repacker)
            .into_iter()
            .map(|p| p.into())
            .collect()
    }
}

impl<'tcx> HasPcsElems<MaybeOldPlace<'tcx>> for DerefExpansion<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        vec![&mut self.base]
    }
}

impl<'tcx> ToJsonWithRepacker<'tcx> for DerefExpansion<'tcx> {
    fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        json!({
            "base": self.base().to_json(repacker),
            "expansion": self.expansion(repacker).iter().map(|p| p.to_json(repacker)).collect::<Vec<_>>(),
        })
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub enum DerefSource<'tcx> {
    Place(MaybeOldPlace<'tcx>),
    RegionProjection(RegionProjection<'tcx>),
}

impl<'tcx> HasPcsElems<MaybeOldPlace<'tcx>> for DerefSource<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        match self {
            DerefSource::Place(p) => vec![p],
            DerefSource::RegionProjection(p) => p.pcs_elems(),
        }
    }
}
