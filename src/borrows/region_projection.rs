use std::fmt;

use crate::rustc_interface::{
    ast::Mutability,
    data_structures::fx::FxHashSet,
    middle::mir::Local,
    middle::ty::{self, DebruijnIndex, RegionVid},
};

use crate::utils::{Place, PlaceRepacker};

use super::{domain::MaybeOldPlace, latest::Latest};
use super::{domain::MaybeRemotePlace, has_pcs_elem::HasPcsElems};

/// A region occuring in region projections
#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub enum PCGRegion {
    RegionVid(RegionVid),
    ReErased,
    /// TODO: Do we need this?
    ReBound(DebruijnIndex, ty::BoundRegion),
}

impl<'tcx> std::fmt::Display for PCGRegion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PCGRegion::RegionVid(vid) => write!(f, "{:?}", vid),
            PCGRegion::ReErased => write!(f, "ReErased"),
            PCGRegion::ReBound(debruijn_index, region) => {
                write!(f, "ReBound({:?}, {:?})", debruijn_index, region)
            }
        }
    }
}

impl PCGRegion {
    pub fn as_vid(&self) -> Option<RegionVid> {
        match self {
            PCGRegion::RegionVid(vid) => Some(*vid),
            _ => None,
        }
    }
}

impl<'tcx> From<ty::Region<'tcx>> for PCGRegion {
    fn from(region: ty::Region<'tcx>) -> Self {
        match region.kind() {
            ty::RegionKind::ReVar(vid) => PCGRegion::RegionVid(vid),
            ty::RegionKind::ReErased => PCGRegion::ReErased,
            ty::RegionKind::ReEarlyParam(_) => todo!(),
            ty::RegionKind::ReBound(debruijn_index, inner) => {
                PCGRegion::ReBound(debruijn_index, inner)
            }
            ty::RegionKind::ReLateParam(_) => todo!(),
            ty::RegionKind::ReStatic => todo!(),
            ty::RegionKind::RePlaceholder(_) => todo!(),
            ty::RegionKind::ReError(_) => todo!(),
        }
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy)]
pub struct RegionProjection<'tcx> {
    pub(crate) place: MaybeRemotePlace<'tcx>,
    region: PCGRegion,
}

impl<'tcx> fmt::Display for RegionProjection<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}↓{}", self.place, self.region)
    }
}

impl<'tcx> RegionProjection<'tcx> {
    pub fn local(&self) -> Option<Local> {
        self.place.as_local_place().map(|p| p.local())
    }

    /// Returns `true` iff the place is a mutable reference, or if the place is
    /// a mutable struct. If the place is a remote place, it is mutable iff the
    /// corresponding input argument is a mutable reference.
    pub(crate) fn mutability(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Mutability {
        let place = match self.place {
            MaybeRemotePlace::Local(p) => p.place(),
            MaybeRemotePlace::Remote(rp) => rp.assigned_local().into(),
        };
        place.ref_mutability(repacker).unwrap_or_else(|| {
            if let Ok(root_place) =
                place.is_mutable(crate::utils::LocalMutationIsAllowed::Yes, repacker)
                && root_place.is_local_mutation_allowed == crate::utils::LocalMutationIsAllowed::Yes
            {
                Mutability::Mut
            } else {
                Mutability::Not
            }
        })
    }

    pub(crate) fn new(region: PCGRegion, place: MaybeRemotePlace<'tcx>) -> Self {
        Self { place, region }
    }

    // pub (crate) fn index(&self, repacker: PlaceRepacker<'_, 'tcx>) -> usize {
    //     self.place
    //         .place()
    //         .projection_index(self.region, repacker)
    //         .unwrap()
    // }

    pub fn deref(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Option<MaybeOldPlace<'tcx>> {
        if let MaybeRemotePlace::Local(p) = &self.place {
            if p.ty_region(repacker) == Some(self.region) {
                Some(p.project_deref(repacker))
            } else {
                None
            }
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
        if let MaybeRemotePlace::Local(p) = &self.place {
            let prefix = p.prefix_place(repacker)?;
            Some(RegionProjection::new(self.region, prefix.into()))
        } else {
            None
        }
    }
}

impl<'tcx> HasPcsElems<MaybeOldPlace<'tcx>> for RegionProjection<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        self.place.pcs_elems()
    }
}
