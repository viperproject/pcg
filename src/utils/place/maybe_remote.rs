use crate::borrow_pcg::has_pcs_elem::HasPcsElems;
use crate::borrow_pcg::region_projection::{
    MaybeRemoteRegionProjectionBase, PCGRegion, RegionIdx, RegionProjectionBaseLike,
};
use crate::combined_pcs::{PCGNode, PCGNodeLike};
use crate::rustc_interface::ast::Mutability;
use crate::rustc_interface::index::IndexVec;
use crate::rustc_interface::middle::{mir, ty};
use crate::utils::display::DisplayWithRepacker;
use crate::utils::json::ToJsonWithRepacker;
use crate::utils::place::maybe_old::MaybeOldPlace;
use crate::utils::place::remote::RemotePlace;
use crate::utils::{HasPlace, Place, PlaceRepacker};

#[derive(PartialEq, Eq, Copy, Clone, Debug, Hash, PartialOrd, Ord)]
pub enum MaybeRemotePlace<'tcx> {
    /// A place that has a name in the program
    Local(MaybeOldPlace<'tcx>),

    /// A place that cannot be named, e.g. the source of a reference-type input argument
    Remote(RemotePlace),
}

impl<'tcx> PCGNodeLike<'tcx> for MaybeRemotePlace<'tcx> {
    fn to_pcg_node(self) -> PCGNode<'tcx> {
        match self {
            MaybeRemotePlace::Local(p) => p.to_pcg_node(),
            MaybeRemotePlace::Remote(rp) => rp.into(),
        }
    }
}

impl<'tcx> RegionProjectionBaseLike<'tcx> for MaybeRemotePlace<'tcx> {
    fn regions(&self, repacker: PlaceRepacker<'_, 'tcx>) -> IndexVec<RegionIdx, PCGRegion> {
        self.related_local_place().regions(repacker)
    }

    fn to_maybe_remote_region_projection_base(&self) -> MaybeRemoteRegionProjectionBase<'tcx> {
        match self {
            MaybeRemotePlace::Local(p) => p.to_maybe_remote_region_projection_base(),
            MaybeRemotePlace::Remote(rp) => (*rp).into(),
        }
    }
}

impl<'tcx> DisplayWithRepacker<'tcx> for MaybeRemotePlace<'tcx> {
    fn to_short_string(&self, repacker: PlaceRepacker<'_, 'tcx>) -> String {
        match self {
            MaybeRemotePlace::Local(p) => p.to_short_string(repacker),
            MaybeRemotePlace::Remote(rp) => format!("{}", rp),
        }
    }
}

impl<'tcx> ToJsonWithRepacker<'tcx> for MaybeRemotePlace<'tcx> {
    fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        match self {
            MaybeRemotePlace::Local(p) => p.to_json(repacker),
            MaybeRemotePlace::Remote(rp) => format!("{}", rp).into(),
        }
    }
}

impl<'tcx> From<RemotePlace> for MaybeRemotePlace<'tcx> {
    fn from(remote_place: RemotePlace) -> Self {
        MaybeRemotePlace::Remote(remote_place)
    }
}

impl<'tcx> HasPcsElems<MaybeOldPlace<'tcx>> for MaybeRemotePlace<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        match self {
            MaybeRemotePlace::Local(p) => vec![p],
            MaybeRemotePlace::Remote(_) => vec![],
        }
    }
}

impl<'tcx> std::fmt::Display for MaybeRemotePlace<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MaybeRemotePlace::Local(p) => write!(f, "{}", p),
            MaybeRemotePlace::Remote(l) => write!(f, "Remote({:?})", l),
        }
    }
}

impl<'tcx> MaybeRemotePlace<'tcx> {
    pub(crate) fn ty(&self, repacker: PlaceRepacker<'_, 'tcx>) -> mir::tcx::PlaceTy<'tcx> {
        match self {
            MaybeRemotePlace::Local(p) => p.ty(repacker),
            MaybeRemotePlace::Remote(rp) => mir::tcx::PlaceTy {
                ty: rp.ty(repacker).into(),
                variant_index: None,
            },
        }
    }

    pub(crate) fn mutability(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Mutability {
        match self {
            MaybeRemotePlace::Local(p) => p.mutability(repacker),
            MaybeRemotePlace::Remote(rp) => rp.mutability(repacker),
        }
    }

    pub fn place_assigned_to_local(local: mir::Local) -> Self {
        MaybeRemotePlace::Remote(RemotePlace { local })
    }

    pub(crate) fn is_old(&self) -> bool {
        matches!(self, MaybeRemotePlace::Local(p) if p.is_old())
    }

    pub(crate) fn to_short_string(&self, repacker: PlaceRepacker<'_, 'tcx>) -> String {
        match self {
            MaybeRemotePlace::Local(p) => p.to_short_string(repacker),
            MaybeRemotePlace::Remote(rp) => format!("{}", rp),
        }
    }

    pub(crate) fn related_local_place(&self) -> Place<'tcx> {
        match self {
            MaybeRemotePlace::Local(p) => p.place(),
            MaybeRemotePlace::Remote(rp) => rp.local.into(),
        }
    }

    pub(crate) fn regions(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> IndexVec<RegionIdx, PCGRegion> {
        self.related_local_place().regions(repacker)
    }

    pub(crate) fn as_current_place(&self) -> Option<Place<'tcx>> {
        if let MaybeRemotePlace::Local(MaybeOldPlace::Current { place }) = self {
            Some(*place)
        } else {
            None
        }
    }

    pub fn as_local_place(&self) -> Option<MaybeOldPlace<'tcx>> {
        match self {
            MaybeRemotePlace::Local(p) => Some(*p),
            MaybeRemotePlace::Remote(_) => None,
        }
    }

    pub fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        match self {
            MaybeRemotePlace::Local(p) => p.to_json(repacker),
            MaybeRemotePlace::Remote(_) => todo!(),
        }
    }

    pub(crate) fn is_owned(&self, repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        self.as_local_place()
            .map(|p| p.is_owned(repacker))
            .unwrap_or(false)
    }
}

impl<'tcx> From<MaybeOldPlace<'tcx>> for MaybeRemotePlace<'tcx> {
    fn from(place: MaybeOldPlace<'tcx>) -> Self {
        MaybeRemotePlace::Local(place)
    }
}

impl<'tcx> From<Place<'tcx>> for MaybeRemotePlace<'tcx> {
    fn from(place: Place<'tcx>) -> Self {
        MaybeRemotePlace::Local(place.into())
    }
}

impl<'tcx> From<mir::Place<'tcx>> for MaybeRemotePlace<'tcx> {
    fn from(place: mir::Place<'tcx>) -> Self {
        MaybeRemotePlace::Local(place.into())
    }
}

impl RemotePlace {
    pub(crate) fn new(local: mir::Local) -> Self {
        Self { local }
    }

    pub(crate) fn assigned_local(self) -> mir::Local {
        self.local
    }

    pub(crate) fn ty<'mir, 'tcx>(&self, repacker: PlaceRepacker<'mir, 'tcx>) -> ty::Ty<'tcx> {
        let place: Place<'_> = self.local.into();
        match place.ty(repacker).ty.kind() {
            ty::TyKind::Ref(_, ty, _) => *ty,
            _ => todo!(),
        }
    }

    pub(crate) fn mutability(&self, repacker: PlaceRepacker<'_, '_>) -> Mutability {
        let place: Place<'_> = self.local.into();
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
}
