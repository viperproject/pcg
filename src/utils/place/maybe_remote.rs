use derive_more::From;

use crate::HasCompilerCtxt;
use crate::borrow_pcg::edge_data::LabelPlacePredicate;
use crate::borrow_pcg::graph::loop_abstraction::MaybeRemoteCurrentPlace;
use crate::borrow_pcg::has_pcs_elem::{LabelNodeContext, LabelPlaceWithContext, PlaceLabeller};
use crate::borrow_pcg::region_projection::{
    MaybeRemoteRegionProjectionBase, PcgRegion, RegionIdx, RegionProjectionBaseLike,
};
use crate::pcg::{PCGNodeLike, PcgNode};
use crate::rustc_interface::index::IndexVec;
use crate::rustc_interface::middle::{mir, ty};
use crate::utils::display::DisplayWithCompilerCtxt;
use crate::utils::json::ToJsonWithCompilerCtxt;
use crate::utils::place::maybe_old::MaybeLabelledPlace;
use crate::utils::place::remote::RemotePlace;
use crate::utils::{CompilerCtxt, HasPlace, LabelledPlace, Place};

#[derive(From, PartialEq, Eq, Copy, Clone, Debug, Hash, PartialOrd, Ord)]
pub enum MaybeRemotePlace<'tcx> {
    /// A place that has a name in the program
    Local(MaybeLabelledPlace<'tcx>),

    /// A place that cannot be named, e.g. the source of a reference-type input argument
    Remote(RemotePlace),
}

impl<'tcx> LabelPlaceWithContext<'tcx, LabelNodeContext> for MaybeRemotePlace<'tcx> {
    fn label_place_with_context(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        label_context: LabelNodeContext,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        match self {
            MaybeRemotePlace::Local(p) => {
                p.label_place_with_context(predicate, labeller, label_context, ctxt)
            }
            MaybeRemotePlace::Remote(_) => false,
        }
    }
}

impl<'tcx> MaybeRemotePlace<'tcx> {
    pub(crate) fn maybe_remote_current_place(&self) -> Option<MaybeRemoteCurrentPlace<'tcx>> {
        match self {
            MaybeRemotePlace::Local(MaybeLabelledPlace::Current(place)) => {
                Some(MaybeRemoteCurrentPlace::Local(*place))
            }
            MaybeRemotePlace::Local(MaybeLabelledPlace::Labelled(_)) => None,
            MaybeRemotePlace::Remote(rp) => Some(MaybeRemoteCurrentPlace::Remote(*rp)),
        }
    }

    pub(crate) fn is_mutable<'a>(&self, ctxt: impl HasCompilerCtxt<'a, 'tcx>) -> bool
    where
        'tcx: 'a,
    {
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
    fn to_pcg_node<C: Copy>(self, repacker: CompilerCtxt<'_, 'tcx, C>) -> PcgNode<'tcx> {
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
        if let MaybeRemotePlace::Local(MaybeLabelledPlace::Current(place)) = self {
            Some(*place)
        } else {
            None
        }
    }

    pub(crate) fn as_local_place_mut(&mut self) -> Option<&mut MaybeLabelledPlace<'tcx>> {
        match self {
            MaybeRemotePlace::Local(p) => Some(p),
            MaybeRemotePlace::Remote(_) => None,
        }
    }

    pub fn as_local_place(&self) -> Option<MaybeLabelledPlace<'tcx>> {
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

impl<'tcx> From<LabelledPlace<'tcx>> for MaybeRemotePlace<'tcx> {
    fn from(place: LabelledPlace<'tcx>) -> Self {
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
            _ => None,
        }
    }
}
