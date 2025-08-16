use crate::borrow_pcg::borrow_pcg_edge::LocalNode;
use crate::borrow_pcg::edge_data::LabelPlacePredicate;
use crate::borrow_pcg::has_pcs_elem::{LabelNodeContext, LabelPlaceWithContext, PlaceLabeller};
use crate::borrow_pcg::region_projection::{
    LifetimeProjection, MaybeRemoteRegionProjectionBase, PcgRegion, RegionIdx,
    RegionProjectionBaseLike,
};
use crate::borrow_pcg::visitor::extract_regions;
use crate::error::PcgError;
use crate::pcg::{LocalNodeLike, MaybeHasLocation, PCGNodeLike, PcgNode};
use crate::rustc_interface::PlaceTy;
use crate::rustc_interface::index::IndexVec;
use crate::rustc_interface::middle::mir;
use crate::rustc_interface::middle::mir::PlaceElem;
use crate::utils::display::DisplayWithCompilerCtxt;
use crate::utils::json::ToJsonWithCompilerCtxt;
use crate::utils::maybe_remote::MaybeRemotePlace;
use crate::utils::validity::HasValidityCheck;
use crate::utils::{
    CompilerCtxt, HasCompilerCtxt, HasPlace, LabelledPlace, Place, SnapshotLocation,
};
use derive_more::{From, TryInto};
use serde_json::json;

#[deprecated(note = "Use MaybeLabelledPlace instead")]
pub type MaybeOldPlace<'tcx> = MaybeLabelledPlace<'tcx>;

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy, From, Ord, PartialOrd, TryInto)]
pub enum MaybeLabelledPlace<'tcx> {
    Current(Place<'tcx>),
    Labelled(LabelledPlace<'tcx>),
}

impl<'tcx> MaybeLabelledPlace<'tcx> {
    pub fn as_current_place(self) -> Option<Place<'tcx>> {
        match self {
            MaybeLabelledPlace::Current(place) => Some(place),
            MaybeLabelledPlace::Labelled(_) => None,
        }
    }

    pub fn is_mutable<'a>(&self, ctxt: impl HasCompilerCtxt<'a, 'tcx>) -> bool
    where
        'tcx: 'a,
    {
        self.place()
            .is_mutable(crate::utils::LocalMutationIsAllowed::Yes, ctxt)
            .is_ok()
    }
}

impl<'tcx> LocalNodeLike<'tcx> for MaybeLabelledPlace<'tcx> {
    fn to_local_node<C: Copy>(self, repacker: CompilerCtxt<'_, 'tcx, C>) -> LocalNode<'tcx> {
        match self {
            MaybeLabelledPlace::Current(place) => place.to_local_node(repacker),
            MaybeLabelledPlace::Labelled(snapshot) => snapshot.to_local_node(repacker),
        }
    }
}

impl<'tcx> RegionProjectionBaseLike<'tcx> for MaybeLabelledPlace<'tcx> {
    fn to_maybe_remote_region_projection_base(&self) -> MaybeRemoteRegionProjectionBase<'tcx> {
        match self {
            MaybeLabelledPlace::Current(place) => place.to_maybe_remote_region_projection_base(),
            MaybeLabelledPlace::Labelled(snapshot) => {
                snapshot.to_maybe_remote_region_projection_base()
            }
        }
    }

    fn regions<C: Copy>(
        &self,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> IndexVec<RegionIdx, PcgRegion> {
        match self {
            MaybeLabelledPlace::Current(place) => place.regions(repacker),
            MaybeLabelledPlace::Labelled(snapshot) => snapshot.place.regions(repacker),
        }
    }
}

impl<'tcx> PCGNodeLike<'tcx> for MaybeLabelledPlace<'tcx> {
    fn to_pcg_node<C: Copy>(self, repacker: CompilerCtxt<'_, 'tcx, C>) -> PcgNode<'tcx> {
        match self {
            MaybeLabelledPlace::Current(place) => place.to_pcg_node(repacker),
            MaybeLabelledPlace::Labelled(snapshot) => snapshot.to_pcg_node(repacker),
        }
    }
}

impl<'tcx> TryFrom<MaybeRemoteRegionProjectionBase<'tcx>> for MaybeLabelledPlace<'tcx> {
    type Error = String;

    fn try_from(value: MaybeRemoteRegionProjectionBase<'tcx>) -> Result<Self, Self::Error> {
        match value {
            MaybeRemoteRegionProjectionBase::Place(maybe_remote_place) => {
                maybe_remote_place.try_into()
            }
            MaybeRemoteRegionProjectionBase::Const(_) => {
                Err("Const cannot be converted to a maybe old place".to_string())
            }
        }
    }
}

impl<'tcx> HasValidityCheck<'tcx> for MaybeLabelledPlace<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        match self {
            MaybeLabelledPlace::Current(place) => place.check_validity(ctxt),
            MaybeLabelledPlace::Labelled(snapshot) => snapshot.check_validity(ctxt),
        }
    }
}

impl<'tcx, BC: Copy> ToJsonWithCompilerCtxt<'tcx, BC> for MaybeLabelledPlace<'tcx> {
    fn to_json(&self, repacker: CompilerCtxt<'_, 'tcx, BC>) -> serde_json::Value {
        match self {
            MaybeLabelledPlace::Current(place) => place.to_json(repacker),
            MaybeLabelledPlace::Labelled(snapshot) => snapshot.to_json(repacker),
        }
    }
}

impl<'tcx> TryFrom<PcgNode<'tcx>> for MaybeLabelledPlace<'tcx> {
    type Error = String;
    fn try_from(node: PcgNode<'tcx>) -> Result<Self, Self::Error> {
        match node {
            PcgNode::Place(p) => Ok(p.try_into()?),
            PcgNode::LifetimeProjection(_) => {
                Err("Region projection cannot be converted to a maybe old place".to_string())
            }
        }
    }
}

impl<'tcx> TryFrom<MaybeRemotePlace<'tcx>> for MaybeLabelledPlace<'tcx> {
    type Error = String;
    fn try_from(remote_place: MaybeRemotePlace<'tcx>) -> Result<Self, Self::Error> {
        match remote_place {
            MaybeRemotePlace::Local(p) => Ok(p),
            MaybeRemotePlace::Remote(r) => Err(format!(
                "Remote place {r:?} cannot be converted to a maybe old place"
            )),
        }
    }
}

impl From<mir::Local> for MaybeLabelledPlace<'_> {
    fn from(local: mir::Local) -> Self {
        Self::Current(local.into())
    }
}

impl<'tcx> From<mir::Place<'tcx>> for MaybeLabelledPlace<'tcx> {
    fn from(place: mir::Place<'tcx>) -> Self {
        Self::Current(place.into())
    }
}

impl std::fmt::Display for MaybeLabelledPlace<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MaybeLabelledPlace::Current(place) => write!(f, "{place:?}"),
            MaybeLabelledPlace::Labelled(old_place) => write!(f, "{old_place}"),
        }
    }
}

impl<'tcx> HasPlace<'tcx> for MaybeLabelledPlace<'tcx> {
    fn place(&self) -> Place<'tcx> {
        match self {
            MaybeLabelledPlace::Current(place) => *place,
            MaybeLabelledPlace::Labelled(old_place) => old_place.place,
        }
    }
    fn place_mut(&mut self) -> &mut Place<'tcx> {
        match self {
            MaybeLabelledPlace::Current(place) => place,
            MaybeLabelledPlace::Labelled(old_place) => &mut old_place.place,
        }
    }

    fn project_deeper<C: Copy>(
        &self,
        elem: PlaceElem<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> Result<Self, PcgError> {
        let mut cloned = *self;
        *cloned.place_mut() = self
            .place()
            .project_deeper(elem, repacker)
            .map_err(PcgError::unsupported)?;
        Ok(cloned)
    }

    fn iter_projections<C: Copy>(
        &self,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> Vec<(Self, PlaceElem<'tcx>)> {
        match self {
            MaybeLabelledPlace::Current(place) => place
                .iter_projections(repacker)
                .into_iter()
                .map(|(p, e)| (p.into(), e))
                .collect(),
            MaybeLabelledPlace::Labelled(old_place) => old_place
                .place
                .iter_projections(repacker)
                .into_iter()
                .map(|(p, e)| (p.into(), e))
                .collect(),
        }
    }

    fn is_place(&self) -> bool {
        true
    }
}

impl<'tcx, BC: Copy> DisplayWithCompilerCtxt<'tcx, BC> for MaybeLabelledPlace<'tcx> {
    fn to_short_string(&self, repacker: CompilerCtxt<'_, 'tcx, BC>) -> String {
        let p = self.place().to_short_string(repacker);
        format!(
            "{}{}",
            p,
            if let Some(location) = self.location() {
                format!(" {location}")
            } else {
                "".to_string()
            }
        )
    }
}

impl MaybeHasLocation for MaybeLabelledPlace<'_> {
    fn location(&self) -> Option<SnapshotLocation> {
        match self {
            MaybeLabelledPlace::Current(_) => None,
            MaybeLabelledPlace::Labelled(old_place) => Some(old_place.at),
        }
    }
}
impl<'tcx> MaybeLabelledPlace<'tcx> {
    pub fn is_old(&self) -> bool {
        matches!(self, MaybeLabelledPlace::Labelled(_))
    }

    pub fn projection(&self) -> &'tcx [PlaceElem<'tcx>] {
        self.place().projection
    }

    pub(crate) fn deref_to_rp<C: Copy>(
        &self,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> Option<LifetimeProjection<'tcx, Self>> {
        if let Some((place, PlaceElem::Deref)) = self.last_projection() {
            place.base_lifetime_projection(repacker)
        } else {
            None
        }
    }

    pub(crate) fn base_lifetime_projection<'a>(
        &self,
        repacker: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Option<LifetimeProjection<'tcx, Self>>
    where
        'tcx: 'a,
    {
        self.place()
            .base_lifetime_projection(repacker)
            .map(|rp| rp.with_base(*self))
    }

    pub(crate) fn is_owned<C: Copy>(&self, repacker: CompilerCtxt<'_, 'tcx, C>) -> bool {
        self.place().is_owned(repacker)
    }

    pub(crate) fn local(&self) -> mir::Local {
        self.place().local
    }

    pub(crate) fn ty_region(&self, repacker: CompilerCtxt<'_, 'tcx>) -> Option<PcgRegion> {
        self.place().ty_region(repacker)
    }

    pub fn last_projection(&self) -> Option<(MaybeLabelledPlace<'tcx>, PlaceElem<'tcx>)> {
        match self {
            MaybeLabelledPlace::Current(place) => {
                place.last_projection().map(|(p, e)| (p.into(), e))
            }
            MaybeLabelledPlace::Labelled(snapshot) => snapshot
                .place
                .last_projection()
                .map(|(p, e)| (LabelledPlace::new(p, snapshot.at).into(), e)),
        }
    }

    pub(crate) fn with_inherent_region<'a>(
        &self,
        repacker: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> MaybeLabelledPlace<'tcx>
    where
        'tcx: 'a,
    {
        match self {
            MaybeLabelledPlace::Current(place) => place.with_inherent_region(repacker).into(),
            MaybeLabelledPlace::Labelled(snapshot) => {
                snapshot.with_inherent_region(repacker).into()
            }
        }
    }

    pub(crate) fn lifetime_projections<'a>(
        &self,
        repacker: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Vec<LifetimeProjection<'tcx, Self>>
    where
        'tcx: 'a,
    {
        let place = self.with_inherent_region(repacker);
        extract_regions(place.ty(repacker).ty, repacker)
            .iter()
            .map(|region| LifetimeProjection::new(*region, place, None, repacker).unwrap())
            .collect()
    }

    pub fn new<T: Into<SnapshotLocation>>(place: Place<'tcx>, at: Option<T>) -> Self {
        if let Some(at) = at {
            Self::Labelled(LabelledPlace::new(place, at))
        } else {
            Self::Current(place)
        }
    }

    pub fn ty<'a>(&self, ctxt: impl HasCompilerCtxt<'a, 'tcx>) -> PlaceTy<'tcx>
    where
        'tcx: 'a,
    {
        self.place().ty(ctxt)
    }

    pub(crate) fn project_deref<BC: Copy>(
        &self,
        repacker: CompilerCtxt<'_, 'tcx, BC>,
    ) -> MaybeLabelledPlace<'tcx> {
        MaybeLabelledPlace::new(self.place().project_deref(repacker), self.location())
    }

    pub fn is_current(&self) -> bool {
        matches!(self, MaybeLabelledPlace::Current { .. })
    }

    pub fn to_json<BC: Copy>(&self, repacker: CompilerCtxt<'_, 'tcx, BC>) -> serde_json::Value {
        json!({
            "place": self.place().to_json(repacker),
            "at": self.location().map(|loc| format!("{loc:?}")),
        })
    }
}

impl<'tcx> LabelPlaceWithContext<'tcx, LabelNodeContext> for MaybeLabelledPlace<'tcx> {
    fn label_place_with_context(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        label_context: LabelNodeContext,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        match self {
            MaybeLabelledPlace::Current(place) => {
                if predicate.applies_to(*place, label_context, ctxt) {
                    *self = MaybeLabelledPlace::Labelled(LabelledPlace::new(
                        *place,
                        labeller.place_label(*place, ctxt),
                    ));
                    true
                } else {
                    false
                }
            }
            _ => false,
        }
    }
}
