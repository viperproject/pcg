use derive_more::From;

use crate::borrow_pcg::graph::loop_abstraction::MaybeRemoteCurrentPlace;
use crate::borrow_pcg::has_pcs_elem::HasPcgElems;
use crate::borrow_pcg::region_projection::{
    MaybeRemoteRegionProjectionBase, PcgRegion, RegionIdx, RegionProjectionBaseLike,
};
use crate::pcg::{PCGNode, PCGNodeLike};
use crate::rustc_interface::index::IndexVec;
use crate::rustc_interface::middle::{mir, ty};
use crate::utils::display::DisplayWithCompilerCtxt;
use crate::utils::json::ToJsonWithCompilerCtxt;
use crate::utils::place::maybe_old::MaybeOldPlace;
use crate::utils::place::remote::RemotePlace;
use crate::utils::{CompilerCtxt, HasPlace, Place, PlaceSnapshot};

#[derive(From, PartialEq, Eq, Copy, Clone, Debug, Hash, PartialOrd, Ord)]
pub enum MaybeRemotePlace<'tcx> {
    /// A place that has a name in the program
    Local(MaybeOldPlace<'tcx>),

    /// A place that cannot be named, e.g. the source of a reference-type input argument
    Remote(RemotePlace),
}

impl<'tcx> MaybeRemotePlace<'tcx> {
    pub(crate) fn maybe_remote_current_place(&self) -> Option<MaybeRemoteCurrentPlace<'tcx>> {
        match self {
            MaybeRemotePlace::Local(MaybeOldPlace::Current { place }) => {
                Some(MaybeRemoteCurrentPlace::Local(*place))
            }
            MaybeRemotePlace::Local(MaybeOldPlace::OldPlace(_)) => None,
            MaybeRemotePlace::Remote(rp) => Some(MaybeRemoteCurrentPlace::Remote(*rp)),
        }
    }

    pub(crate) fn is_mutable(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        match self {
            MaybeRemotePlace::Local(p) => p.is_mutable(ctxt),
            MaybeRemotePlace::Remote(_) => false,
        }
    }
}

impl<'tcx> TryFrom<MaybeRemoteRegionProjectionBase<'tcx>> for MaybeRemotePlace<'tcx> {
    type Error = ();
    fn try_from(value: MaybeRemoteRegionProjectionBase<'tcx>) -> Result<Self, Self::Error> {
        match value {
            MaybeRemoteRegionProjectionBase::Place(maybe_remote_place) => Ok(maybe_remote_place),
            MaybeRemoteRegionProjectionBase::Const(_) => Err(()),
        }
    }
}

impl<'tcx> PCGNodeLike<'tcx> for MaybeRemotePlace<'tcx> {
    fn to_pcg_node<C: Copy>(self, repacker: CompilerCtxt<'_, 'tcx, C>) -> PCGNode<'tcx> {
        match self {
            MaybeRemotePlace::Local(p) => p.to_pcg_node(repacker),
            MaybeRemotePlace::Remote(rp) => rp.to_pcg_node(repacker),
        }
    }
}

impl<'tcx> RegionProjectionBaseLike<'tcx> for MaybeRemotePlace<'tcx> {
    fn to_maybe_remote_region_projection_base(&self) -> MaybeRemoteRegionProjectionBase<'tcx> {
        match self {
            MaybeRemotePlace::Local(p) => p.to_maybe_remote_region_projection_base(),
            MaybeRemotePlace::Remote(rp) => (*rp).into(),
        }
    }

    fn regions<C: Copy>(
        &self,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> IndexVec<RegionIdx, PcgRegion> {
        self.related_local_place().regions(repacker)
    }
}

impl<'tcx, BC: Copy> DisplayWithCompilerCtxt<'tcx, BC> for MaybeRemotePlace<'tcx> {
    fn to_short_string(&self, repacker: CompilerCtxt<'_, 'tcx, BC>) -> String {
        match self {
            MaybeRemotePlace::Local(p) => p.to_short_string(repacker),
            MaybeRemotePlace::Remote(rp) => format!("{rp}"),
        }
    }
}

impl<'tcx, BC: Copy> ToJsonWithCompilerCtxt<'tcx, BC> for MaybeRemotePlace<'tcx> {
    fn to_json(&self, repacker: CompilerCtxt<'_, 'tcx, BC>) -> serde_json::Value {
        match self {
            MaybeRemotePlace::Local(p) => p.to_json(repacker),
            MaybeRemotePlace::Remote(rp) => format!("{rp}").into(),
        }
    }
}

impl<'tcx> HasPcgElems<MaybeOldPlace<'tcx>> for MaybeRemotePlace<'tcx> {
    fn pcg_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        match self {
            MaybeRemotePlace::Local(p) => vec![p],
            MaybeRemotePlace::Remote(_) => vec![],
        }
    }
}

impl std::fmt::Display for MaybeRemotePlace<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MaybeRemotePlace::Local(p) => write!(f, "{p}"),
            MaybeRemotePlace::Remote(l) => write!(f, "Remote({l:?})"),
        }
    }
}

impl<'tcx> MaybeRemotePlace<'tcx> {
    pub fn place_assigned_to_local(local: mir::Local) -> Self {
        MaybeRemotePlace::Remote(RemotePlace { local })
    }

    pub(crate) fn related_local_place(&self) -> Place<'tcx> {
        match self {
            MaybeRemotePlace::Local(p) => p.place(),
            MaybeRemotePlace::Remote(rp) => rp.local.into(),
        }
    }

    pub(crate) fn regions<C: Copy>(
        &self,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> IndexVec<RegionIdx, PcgRegion> {
        self.related_local_place().regions(repacker)
    }

    pub(crate) fn as_current_place(&self) -> Option<Place<'tcx>> {
        if let MaybeRemotePlace::Local(MaybeOldPlace::Current { place }) = self {
            Some(*place)
        } else {
            None
        }
    }

    pub(crate) fn as_local_place_mut(&mut self) -> Option<&mut MaybeOldPlace<'tcx>> {
        match self {
            MaybeRemotePlace::Local(p) => Some(p),
            MaybeRemotePlace::Remote(_) => None,
        }
    }

    pub fn as_local_place(&self) -> Option<MaybeOldPlace<'tcx>> {
        match self {
            MaybeRemotePlace::Local(p) => Some(*p),
            MaybeRemotePlace::Remote(_) => None,
        }
    }

    pub fn to_json(&self, repacker: CompilerCtxt<'_, 'tcx>) -> serde_json::Value {
        match self {
            MaybeRemotePlace::Local(p) => p.to_json(repacker),
            MaybeRemotePlace::Remote(_) => todo!(),
        }
    }
}

impl<'tcx> From<PlaceSnapshot<'tcx>> for MaybeRemotePlace<'tcx> {
    fn from(place: PlaceSnapshot<'tcx>) -> Self {
        MaybeRemotePlace::Local(place.into())
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

    pub fn assigned_local(self) -> mir::Local {
        self.local
    }

    pub(crate) fn ty<'tcx, C: Copy>(
        &self,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> Option<ty::Ty<'tcx>> {
        let place: Place<'_> = self.local.into();
        match place.ty(repacker).ty.kind() {
            ty::TyKind::Ref(_, ty, _) => Some(*ty),
            _ => None
        }
    }
}
