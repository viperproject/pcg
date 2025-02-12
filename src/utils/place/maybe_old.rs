use derive_more::From;
use crate::rustc_interface::index::IndexVec;
use crate::rustc_interface::middle::mir;
use crate::rustc_interface::middle::mir::PlaceElem;
use crate::rustc_interface::ast::Mutability;
use crate::rustc_interface::middle::mir::tcx::PlaceTy;
use serde_json::json;
use crate::borrows::borrow_pcg_edge::LocalNode;
use crate::borrows::borrows_visitor::extract_regions;
use crate::borrows::domain::ToJsonWithRepacker;
use crate::borrows::has_pcs_elem::HasPcsElems;
use crate::borrows::latest::Latest;
use crate::borrows::region_projection::{MaybeRemoteRegionProjectionBase, PCGRegion, RegionIdx, RegionProjection, RegionProjectionBaseLike};
use crate::combined_pcs::{LocalNodeLike, PCGNode, PCGNodeLike};
use crate::utils::{HasPlace, Place, PlaceRepacker, PlaceSnapshot, SnapshotLocation};
use crate::utils::display::DisplayWithRepacker;
use crate::utils::maybe_remote::MaybeRemotePlace;
use crate::utils::validity::HasValidityCheck;

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy, From, Ord, PartialOrd)]
pub enum MaybeOldPlace<'tcx> {
    Current { place: Place<'tcx> },
    OldPlace(PlaceSnapshot<'tcx>),
}

impl<'tcx> LocalNodeLike<'tcx> for MaybeOldPlace<'tcx> {
    fn to_local_node(self) -> LocalNode<'tcx> {
        match self {
            MaybeOldPlace::Current { place } => place.to_local_node(),
            MaybeOldPlace::OldPlace(snapshot) => snapshot.to_local_node(),
        }
    }
}

impl<'tcx> RegionProjectionBaseLike<'tcx> for MaybeOldPlace<'tcx> {
    fn regions(&self, repacker: PlaceRepacker<'_, 'tcx>) -> IndexVec<RegionIdx, PCGRegion> {
        match self {
            MaybeOldPlace::Current { place } => place.regions(repacker),
            MaybeOldPlace::OldPlace(snapshot) => snapshot.place.regions(repacker),
        }
    }

    fn to_maybe_remote_region_projection_base(&self) -> MaybeRemoteRegionProjectionBase<'tcx> {
        match self {
            MaybeOldPlace::Current { place } => place.to_maybe_remote_region_projection_base(),
            MaybeOldPlace::OldPlace(snapshot) => {
                snapshot.place.to_maybe_remote_region_projection_base()
            }
        }
    }
}

impl<'tcx> PCGNodeLike<'tcx> for MaybeOldPlace<'tcx> {
    fn to_pcg_node(self) -> PCGNode<'tcx> {
        match self {
            MaybeOldPlace::Current { place } => place.to_pcg_node(),
            MaybeOldPlace::OldPlace(snapshot) => snapshot.place.to_pcg_node(),
        }
    }
}

impl<'tcx> TryFrom<MaybeRemoteRegionProjectionBase<'tcx>> for MaybeOldPlace<'tcx> {
    type Error = ();

    fn try_from(value: MaybeRemoteRegionProjectionBase<'tcx>) -> Result<Self, Self::Error> {
        match value {
            MaybeRemoteRegionProjectionBase::Place(maybe_remote_place) => {
                maybe_remote_place.try_into()
            }
            MaybeRemoteRegionProjectionBase::Const(_) => Err(()),
        }
    }
}

impl<'tcx> HasValidityCheck<'tcx> for MaybeOldPlace<'tcx> {
    fn check_validity(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Result<(), String> {
        match self {
            MaybeOldPlace::Current { place } => place.check_validity(repacker),
            MaybeOldPlace::OldPlace(snapshot) => snapshot.check_validity(repacker),
        }
    }
}

impl<'tcx> ToJsonWithRepacker<'tcx> for MaybeOldPlace<'tcx> {
    fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        match self {
            MaybeOldPlace::Current { place } => place.to_json(repacker),
            MaybeOldPlace::OldPlace(snapshot) => snapshot.to_json(repacker),
        }
    }
}

impl<'tcx> TryFrom<PCGNode<'tcx>> for MaybeOldPlace<'tcx> {
    type Error = ();
    fn try_from(node: PCGNode<'tcx>) -> Result<Self, Self::Error> {
        match node {
            PCGNode::Place(p) => Ok(p.try_into()?),
            PCGNode::RegionProjection(_) => Err(()),
        }
    }
}

impl<'tcx> TryFrom<MaybeRemotePlace<'tcx>> for MaybeOldPlace<'tcx> {
    type Error = ();
    fn try_from(remote_place: MaybeRemotePlace<'tcx>) -> Result<Self, Self::Error> {
        match remote_place {
            MaybeRemotePlace::Local(p) => Ok(p),
            MaybeRemotePlace::Remote(_) => Err(()),
        }
    }
}

impl<'tcx> From<mir::Local> for MaybeOldPlace<'tcx> {
    fn from(local: mir::Local) -> Self {
        Self::Current {
            place: local.into(),
        }
    }
}

impl<'tcx> From<mir::Place<'tcx>> for MaybeOldPlace<'tcx> {
    fn from(place: mir::Place<'tcx>) -> Self {
        Self::Current {
            place: place.into(),
        }
    }
}

impl<'tcx> std::fmt::Display for MaybeOldPlace<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MaybeOldPlace::Current { place } => write!(f, "{:?}", place),
            MaybeOldPlace::OldPlace(old_place) => write!(f, "{}", old_place),
        }
    }
}

impl<'tcx> HasPlace<'tcx> for MaybeOldPlace<'tcx> {
    fn place(&self) -> Place<'tcx> {
        match self {
            MaybeOldPlace::Current { place } => *place,
            MaybeOldPlace::OldPlace(old_place) => old_place.place,
        }
    }
    fn place_mut(&mut self) -> &mut Place<'tcx> {
        match self {
            MaybeOldPlace::Current { place } => place,
            MaybeOldPlace::OldPlace(old_place) => &mut old_place.place,
        }
    }

    fn project_deeper(&self, repacker: PlaceRepacker<'_, 'tcx>, elem: PlaceElem<'tcx>) -> Self {
        let mut cloned = self.clone();
        *cloned.place_mut() = self.place().project_deeper(repacker, elem);
        cloned
    }
}

impl<'tcx> DisplayWithRepacker<'tcx> for MaybeOldPlace<'tcx> {
    fn to_short_string(&self, repacker: PlaceRepacker<'_, 'tcx>) -> String {
        let p = self.place().to_short_string(repacker);
        format!(
            "{}{}",
            p,
            if let Some(location) = self.location() {
                format!(" at {:?}", location)
            } else {
                "".to_string()
            }
        )
    }
}

impl<'tcx> MaybeOldPlace<'tcx> {
    pub fn is_old(&self) -> bool {
        matches!(self, MaybeOldPlace::OldPlace(_))
    }

    pub fn projection(&self) -> &'tcx [PlaceElem<'tcx>] {
        self.place().projection
    }

    pub(crate) fn mutability(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Mutability {
        let place: Place<'_> = self.place();
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
    pub(crate) fn is_owned(&self, repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        self.place().is_owned(repacker)
    }

    pub(crate) fn local(&self) -> mir::Local {
        self.place().local
    }

    pub(crate) fn ty_region(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Option<PCGRegion> {
        self.place().ty_region(repacker)
    }

    pub fn last_projection(&self) -> Option<(Place<'tcx>, PlaceElem<'tcx>)> {
        match self {
            MaybeOldPlace::Current { place } => place.last_projection(),
            MaybeOldPlace::OldPlace(snapshot) => snapshot.place.last_projection(),
        }
    }

    pub(crate) fn with_inherent_region(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> MaybeOldPlace<'tcx> {
        match self {
            MaybeOldPlace::Current { place } => place.with_inherent_region(repacker).into(),
            MaybeOldPlace::OldPlace(snapshot) => snapshot.with_inherent_region(repacker).into(),
        }
    }

    pub(crate) fn region_projection(
        &self,
        idx: usize,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> RegionProjection<'tcx, Self> {
        let region_projections = self.region_projections(repacker);
        if idx < region_projections.len() {
            region_projections[idx]
        } else {
            panic!(
                "Region projection index {:?} out of bounds for place {:?}, ty: {:?}",
                idx,
                self,
                self.ty(repacker)
            );
        }
    }

    pub(crate) fn region_projections(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Vec<RegionProjection<'tcx, Self>> {
        let place = self.with_inherent_region(repacker);
        extract_regions(place.ty(repacker).ty)
            .iter()
            .map(|region| RegionProjection::new((*region).into(), place.into(), repacker))
            .collect()
    }

    pub fn new<T: Into<SnapshotLocation>>(place: Place<'tcx>, at: Option<T>) -> Self {
        if let Some(at) = at {
            Self::OldPlace(PlaceSnapshot::new(place, at))
        } else {
            Self::Current { place }
        }
    }

    pub fn ty(&self, repacker: PlaceRepacker<'_, 'tcx>) -> PlaceTy<'tcx> {
        self.place().ty(repacker)
    }

    pub(crate) fn project_deref(&self, repacker: PlaceRepacker<'_, 'tcx>) -> MaybeOldPlace<'tcx> {
        MaybeOldPlace::new(self.place().project_deref(repacker).into(), self.location())
    }

    pub fn is_current(&self) -> bool {
        matches!(self, MaybeOldPlace::Current { .. })
    }

    pub fn location(&self) -> Option<SnapshotLocation> {
        match self {
            MaybeOldPlace::Current { .. } => None,
            MaybeOldPlace::OldPlace(old_place) => Some(old_place.at),
        }
    }

    pub fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        json!({
            "place": self.place().to_json(repacker),
            "at": self.location().map(|loc| format!("{:?}", loc)),
        })
    }

    pub(crate) fn make_place_old(&mut self, place: Place<'tcx>, latest: &Latest<'tcx>) -> bool {
        if self.is_current() && place.is_prefix(self.place()) {
            *self = MaybeOldPlace::OldPlace(PlaceSnapshot {
                place: self.place(),
                at: latest.get(self.place()),
            });
            true
        } else {
            false
        }
    }
}

impl<'tcx> HasPcsElems<Place<'tcx>> for MaybeOldPlace<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut Place<'tcx>> {
        match self {
            MaybeOldPlace::Current { place } => vec![place],
            MaybeOldPlace::OldPlace(snapshot) => snapshot.pcs_elems(),
        }
    }
}