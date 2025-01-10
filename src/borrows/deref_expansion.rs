use serde_json::json;

use crate::{
    edgedata_enum,
    rustc_interface::{
        data_structures::fx::FxHashSet,
        middle::mir::{Location, PlaceElem},
    },
    utils::{Place, PlaceRepacker, PlaceSnapshot, SnapshotLocation},
};

use super::{
    borrow_pcg_edge::{BlockingNode, PCGNode},
    domain::{MaybeOldPlace, ToJsonWithRepacker},
    edge_data::EdgeData,
    has_pcs_elem::HasPcsElems,
    region_projection::RegionProjection,
};

/// An expansion of a place in the PCS
#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct BorrowDerefExpansion<'tcx> {
    base: MaybeOldPlace<'tcx>,
    expansion: Vec<PlaceElem<'tcx>>,
    pub location: Location,
}

impl<'tcx> BorrowDerefExpansion<'tcx> {
    pub fn base(&self) -> MaybeOldPlace<'tcx> {
        self.base
    }

    pub fn expansion(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Vec<MaybeOldPlace<'tcx>> {
        self.expansion
            .iter()
            .map(|p| self.base.project_deeper(repacker.tcx(), *p))
            .collect()
    }
}

impl<'tcx> HasPcsElems<MaybeOldPlace<'tcx>> for BorrowDerefExpansion<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        vec![&mut self.base]
    }
}

impl<'tcx> EdgeData<'tcx> for BorrowDerefExpansion<'tcx> {
    fn blocked_nodes(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<PCGNode<'tcx>> {
        vec![self.base.into()].into_iter().collect()
    }

    fn blocked_by_nodes(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> FxHashSet<super::borrow_pcg_edge::LocalNode<'tcx>> {
        self.expansion(repacker)
            .into_iter()
            .map(|p| p.into())
            .collect()
    }

    fn is_owned_expansion(&self) -> bool {
        todo!()
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct OwnedExpansion<'tcx> {
    base: MaybeOldPlace<'tcx>,
}

impl<'tcx> EdgeData<'tcx> for OwnedExpansion<'tcx> {
    fn blocked_nodes(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> FxHashSet<super::borrow_pcg_edge::PCGNode<'tcx>> {
        let mut blocked_nodes = vec![self.base.into()];
        if self.base.has_region_projections(repacker) {
            blocked_nodes.push(self.base_region_projection(repacker).into());
        }
        blocked_nodes.into_iter().collect()
    }

    fn blocked_by_nodes(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> FxHashSet<super::borrow_pcg_edge::LocalNode<'tcx>> {
        vec![self.expansion(repacker)]
            .into_iter()
            .map(|p| p.into())
            .collect()
    }

    fn is_owned_expansion(&self) -> bool {
        true
    }
}

impl<'tcx> OwnedExpansion<'tcx> {
    pub fn new(base: MaybeOldPlace<'tcx>) -> Self {
        Self { base }
    }

    pub fn base(&self) -> MaybeOldPlace<'tcx> {
        self.base
    }

    pub fn expansion(&self, repacker: PlaceRepacker<'_, 'tcx>) -> MaybeOldPlace<'tcx> {
        self.base.project_deref(repacker)
    }

    pub fn base_region_projection(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> RegionProjection<'tcx> {
        self.base.region_projection(0, repacker)
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub enum DerefExpansion<'tcx> {
    /// An expansion of a place in the FPCS
    OwnedExpansion(OwnedExpansion<'tcx>),
    /// An expansion of a place in the PCS
    BorrowExpansion(BorrowDerefExpansion<'tcx>),
}

edgedata_enum!(
    DerefExpansion<'tcx>,
    OwnedExpansion(OwnedExpansion<'tcx>),
    BorrowExpansion(BorrowDerefExpansion<'tcx>)
);

impl<'tcx> HasPcsElems<MaybeOldPlace<'tcx>> for OwnedExpansion<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        vec![&mut self.base]
    }
}

impl<'tcx> HasPcsElems<MaybeOldPlace<'tcx>> for DerefExpansion<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        match self {
            DerefExpansion::OwnedExpansion(owned) => owned.pcs_elems(),
            DerefExpansion::BorrowExpansion(e) => e.pcs_elems(),
        }
    }
}

impl<'tcx> DerefExpansion<'tcx> {
    pub fn blocked_by_nodes(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> FxHashSet<BlockingNode<'tcx>> {
        self.expansion(repacker)
            .into_iter()
            .map(|p| p.into())
            .collect()
    }

    pub fn mut_base(&mut self) -> &mut MaybeOldPlace<'tcx> {
        match self {
            DerefExpansion::OwnedExpansion(owned) => &mut owned.base,
            DerefExpansion::BorrowExpansion(e) => &mut e.base,
        }
    }

    pub fn is_owned_expansion(&self) -> bool {
        matches!(self, DerefExpansion::OwnedExpansion { .. })
    }

    pub fn borrow_expansion(&self) -> Option<&BorrowDerefExpansion<'tcx>> {
        match self {
            DerefExpansion::BorrowExpansion(e) => Some(e),
            _ => None,
        }
    }

    pub fn borrowed(
        base: MaybeOldPlace<'tcx>,
        expansion: Vec<Place<'tcx>>,
        location: Location,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Self {
        assert!(!base.place().is_owned(repacker));
        assert!(expansion.iter().all(|p| base.place().is_prefix(*p)
            && p.projection.len() == base.place().projection.len() + 1));
        DerefExpansion::BorrowExpansion(BorrowDerefExpansion {
            base,
            expansion: expansion
                .into_iter()
                .map(|p| p.projection.last().unwrap())
                .copied()
                .collect(),
            location,
        })
    }

    pub fn base(&self) -> MaybeOldPlace<'tcx> {
        match self {
            DerefExpansion::OwnedExpansion(owned) => owned.base(),
            DerefExpansion::BorrowExpansion(e) => e.base,
        }
    }

    pub fn set_base(&mut self, base: MaybeOldPlace<'tcx>) {
        match self {
            DerefExpansion::OwnedExpansion(owned) => {
                owned.base = base;
            }
            DerefExpansion::BorrowExpansion(e) => {
                e.base = base;
            }
        }
    }

    pub fn make_base_old(&mut self, place_location: SnapshotLocation) {
        let base = self.base();
        assert!(base.is_current());
        self.set_base(MaybeOldPlace::OldPlace(PlaceSnapshot {
            place: base.place(),
            at: place_location,
        }));
    }

    pub fn expansion_elems(&self) -> Vec<PlaceElem<'tcx>> {
        match self {
            DerefExpansion::OwnedExpansion { .. } => vec![PlaceElem::Deref],
            DerefExpansion::BorrowExpansion(e) => e.expansion.clone(),
        }
    }

    pub fn expansion(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Vec<MaybeOldPlace<'tcx>> {
        match self {
            DerefExpansion::OwnedExpansion(owned) => vec![owned.expansion(repacker)],
            DerefExpansion::BorrowExpansion(e) => e.expansion(repacker),
        }
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
