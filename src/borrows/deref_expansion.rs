use serde_json::json;

use crate::{
    rustc_interface::{
        data_structures::fx::FxHashSet,
        middle::mir::{Location, PlaceElem},
    },
    utils::{Place, PlaceRepacker, PlaceSnapshot, SnapshotLocation},
};

use super::{
    domain::{MaybeOldPlace, ToJsonWithRepacker},
    latest::Latest,
    region_projection::RegionProjection,
};
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

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub enum DerefExpansion<'tcx> {
    OwnedExpansion { base: MaybeOldPlace<'tcx> },
    BorrowExpansion(BorrowDerefExpansion<'tcx>),
}

impl<'tcx> DerefExpansion<'tcx> {
    pub fn region_projection_edges(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> FxHashSet<(RegionProjection<'tcx>, RegionProjection<'tcx>)> {
        let mut edges = FxHashSet::default();
        for rp in self.expansion(repacker).iter() {
            edges.extend(RegionProjection::connections_between_places(
                self.base(),
                rp.clone(),
                repacker,
            ));
        }
        edges
    }

    pub fn mut_base(&mut self) -> &mut MaybeOldPlace<'tcx> {
        match self {
            DerefExpansion::OwnedExpansion { base, .. } => base,
            DerefExpansion::BorrowExpansion(e) => &mut e.base,
        }
    }

    pub fn is_owned_expansion(&self) -> bool {
        matches!(self, DerefExpansion::OwnedExpansion { .. })
    }

    pub fn make_place_old(&mut self, place: Place<'tcx>, latest: &Latest) {
        match self {
            DerefExpansion::OwnedExpansion { base, .. } => base.make_place_old(place, latest),
            DerefExpansion::BorrowExpansion(e) => e.base.make_place_old(place, latest),
        }
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
        assert!(!base.place().is_owned(repacker.body(), repacker.tcx()));
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
            DerefExpansion::OwnedExpansion { base, .. } => *base,
            DerefExpansion::BorrowExpansion(e) => e.base,
        }
    }

    pub fn set_base(&mut self, base: MaybeOldPlace<'tcx>) {
        match self {
            DerefExpansion::OwnedExpansion { base: b, .. } => {
                *b = base;
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
            DerefExpansion::OwnedExpansion { base, .. } => vec![base.project_deref(repacker)],
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
