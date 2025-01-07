use std::fmt;

use crate::rustc_interface::{
    ast::Mutability,
    data_structures::fx::FxHashSet,
    middle::mir::Local,
    middle::ty::{self, RegionVid},
};

use crate::utils::{Place, PlaceRepacker};

use super::has_pcs_elem::HasPcsElems;
use super::{domain::MaybeOldPlace, latest::Latest};

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy)]
pub enum PCGRegion {
    RegionVid(RegionVid),
    ReErased,
}

impl std::fmt::Display for PCGRegion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PCGRegion::RegionVid(vid) => write!(f, "{:?}", vid),
            PCGRegion::ReErased => write!(f, "ReErased"),
        }
    }
}

impl PCGRegion {
    pub fn as_vid(&self) -> Option<RegionVid> {
        match self {
            PCGRegion::RegionVid(vid) => Some(*vid),
            PCGRegion::ReErased => None,
        }
    }
}

impl<'tcx> From<ty::Region<'tcx>> for PCGRegion {
    fn from(region: ty::Region<'tcx>) -> Self {
        match region.kind() {
            ty::RegionKind::ReVar(vid) => PCGRegion::RegionVid(vid),
            ty::RegionKind::ReErased => PCGRegion::ReErased,
            _ => todo!(),
        }
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy)]
pub struct RegionProjection<'tcx> {
    pub place: MaybeOldPlace<'tcx>,
    region: PCGRegion,
}

impl<'tcx> fmt::Display for RegionProjection<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}↓{}", self.place, self.region)
    }
}

impl<'tcx> RegionProjection<'tcx> {
    pub fn local(&self) -> Local {
        self.place.local()
    }

    /// Returns `true` iff the place is a mutable reference, or if the place is
    /// a mutable struct.
    pub fn mutability(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Mutability {
        self.place.ref_mutability(repacker).unwrap_or(
            if {
                self.place
                    .place()
                    .is_mutable(crate::utils::LocalMutationIsAllowed::Yes, repacker)
                    .unwrap()
                    .is_local_mutation_allowed
                    == crate::utils::LocalMutationIsAllowed::Yes
            } {
                Mutability::Mut
            } else {
                Mutability::Not
            },
        )
    }

    pub fn new(region: PCGRegion, place: MaybeOldPlace<'tcx>) -> Self {
        Self { place, region }
    }

    pub fn make_place_old(&mut self, place: Place<'tcx>, latest: &Latest<'tcx>) {
        self.place.make_place_old(place, latest);
    }

    pub fn index(&self, repacker: PlaceRepacker<'_, 'tcx>) -> usize {
        self.place
            .place()
            .projection_index(self.region, repacker)
            .unwrap()
    }

    pub fn deref(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Option<MaybeOldPlace<'tcx>> {
        if self.place.ty_region(repacker) == Some(self.region) {
            Some(self.place.project_deref(repacker))
        } else {
            None
        }
    }

    pub fn region(&self) -> PCGRegion {
        self.region
    }

    pub fn connections_between_places(
        source: MaybeOldPlace<'tcx>,
        dest: MaybeOldPlace<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> FxHashSet<(RegionProjection<'tcx>, RegionProjection<'tcx>)> {
        let mut edges = FxHashSet::default();
        for rp in source.region_projections(repacker) {
            for erp in dest.region_projections(repacker) {
                edges.insert((rp, erp));
            }
        }
        edges
    }

    pub fn prefix_projection(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Option<RegionProjection<'tcx>> {
        let prefix = self.place.prefix_place(repacker)?;
        Some(RegionProjection::new(self.region, prefix))
    }
}

impl<'tcx> HasPcsElems<MaybeOldPlace<'tcx>> for RegionProjection<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        vec![&mut self.place]
    }
}
