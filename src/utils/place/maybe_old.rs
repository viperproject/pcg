use crate::borrow_pcg::borrow_pcg_edge::LocalNode;
use crate::borrow_pcg::edge_data::LabelPlacePredicate;
use crate::borrow_pcg::has_pcs_elem::{HasPcgElems, LabelPlace};
use crate::borrow_pcg::latest::Latest;
use crate::borrow_pcg::region_projection::{
    MaybeRemoteRegionProjectionBase, PcgRegion, RegionIdx, RegionProjection,
    RegionProjectionBaseLike,
};
use crate::borrow_pcg::visitor::extract_regions;
use crate::pcg::{LocalNodeLike, MaybeHasLocation, PCGNode, PCGNodeLike, PcgError};
use crate::rustc_interface::index::IndexVec;
use crate::rustc_interface::middle::mir;
use crate::rustc_interface::middle::mir::PlaceElem;
use crate::rustc_interface::PlaceTy;
use crate::utils::display::DisplayWithCompilerCtxt;
use crate::utils::json::ToJsonWithCompilerCtxt;
use crate::utils::maybe_remote::MaybeRemotePlace;
use crate::utils::validity::HasValidityCheck;
use crate::utils::{CompilerCtxt, HasPlace, Place, PlaceSnapshot, SnapshotLocation};
use derive_more::{From, TryInto};
use serde_json::json;

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy, From, Ord, PartialOrd, TryInto)]
pub enum MaybeOldPlace<'tcx> {
    Current { place: Place<'tcx> },
    OldPlace(PlaceSnapshot<'tcx>),
}

impl<'tcx> LocalNodeLike<'tcx> for MaybeOldPlace<'tcx> {
    fn to_local_node<C: Copy>(self, repacker: CompilerCtxt<'_, 'tcx, C>) -> LocalNode<'tcx> {
        match self {
            MaybeOldPlace::Current { place } => place.to_local_node(repacker),
            MaybeOldPlace::OldPlace(snapshot) => snapshot.to_local_node(repacker),
        }
    }
}

impl<'tcx> RegionProjectionBaseLike<'tcx> for MaybeOldPlace<'tcx> {
    fn to_maybe_remote_region_projection_base(&self) -> MaybeRemoteRegionProjectionBase<'tcx> {
        match self {
            MaybeOldPlace::Current { place } => place.to_maybe_remote_region_projection_base(),
            MaybeOldPlace::OldPlace(snapshot) => snapshot.to_maybe_remote_region_projection_base(),
        }
    }

    fn regions<C: Copy>(
        &self,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> IndexVec<RegionIdx, PcgRegion> {
        match self {
            MaybeOldPlace::Current { place } => place.regions(repacker),
            MaybeOldPlace::OldPlace(snapshot) => snapshot.place.regions(repacker),
        }
    }
}

impl<'tcx> PCGNodeLike<'tcx> for MaybeOldPlace<'tcx> {
    fn to_pcg_node<C: Copy>(self, repacker: CompilerCtxt<'_, 'tcx, C>) -> PCGNode<'tcx> {
        match self {
            MaybeOldPlace::Current { place } => place.to_pcg_node(repacker),
            MaybeOldPlace::OldPlace(snapshot) => snapshot.to_pcg_node(repacker),
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
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        match self {
            MaybeOldPlace::Current { place } => place.check_validity(ctxt),
            MaybeOldPlace::OldPlace(snapshot) => snapshot.check_validity(ctxt),
        }
    }
}

impl<'tcx> ToJsonWithCompilerCtxt<'tcx> for MaybeOldPlace<'tcx> {
    fn to_json(&self, repacker: CompilerCtxt<'_, 'tcx>) -> serde_json::Value {
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

impl From<mir::Local> for MaybeOldPlace<'_> {
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

impl std::fmt::Display for MaybeOldPlace<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MaybeOldPlace::Current { place } => write!(f, "{place:?}"),
            MaybeOldPlace::OldPlace(old_place) => write!(f, "{old_place}"),
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
            MaybeOldPlace::Current { place } => place
                .iter_projections(repacker)
                .into_iter()
                .map(|(p, e)| (p.into(), e))
                .collect(),
            MaybeOldPlace::OldPlace(old_place) => old_place
                .place
                .iter_projections(repacker)
                .into_iter()
                .map(|(p, e)| (p.into(), e))
                .collect(),
        }
    }
}

impl<'tcx> DisplayWithCompilerCtxt<'tcx> for MaybeOldPlace<'tcx> {
    fn to_short_string(&self, repacker: CompilerCtxt<'_, 'tcx>) -> String {
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

impl MaybeHasLocation for MaybeOldPlace<'_> {
    fn location(&self) -> Option<SnapshotLocation> {
        match self {
            MaybeOldPlace::Current { .. } => None,
            MaybeOldPlace::OldPlace(old_place) => Some(old_place.at),
        }
    }
}
impl<'tcx> MaybeOldPlace<'tcx> {
    pub fn is_old(&self) -> bool {
        matches!(self, MaybeOldPlace::OldPlace(_))
    }

    pub fn projection(&self) -> &'tcx [PlaceElem<'tcx>] {
        self.place().projection
    }

    pub(crate) fn deref_to_rp<C: Copy>(
        &self,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> Option<RegionProjection<'tcx, Self>> {
        if let Some((place, PlaceElem::Deref)) = self.last_projection() {
            place.base_region_projection(repacker)
        } else {
            None
        }
    }

    pub(crate) fn base_region_projection<C: Copy>(
        &self,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> Option<RegionProjection<'tcx, Self>> {
        self.place()
            .base_region_projection(repacker)
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

    pub fn last_projection(&self) -> Option<(MaybeOldPlace<'tcx>, PlaceElem<'tcx>)> {
        match self {
            MaybeOldPlace::Current { place } => place.last_projection().map(|(p, e)| (p.into(), e)),
            MaybeOldPlace::OldPlace(snapshot) => snapshot
                .place
                .last_projection()
                .map(|(p, e)| (PlaceSnapshot::new(p, snapshot.at).into(), e)),
        }
    }

    pub(crate) fn with_inherent_region(
        &self,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> MaybeOldPlace<'tcx> {
        match self {
            MaybeOldPlace::Current { place } => place.with_inherent_region(repacker).into(),
            MaybeOldPlace::OldPlace(snapshot) => snapshot.with_inherent_region(repacker).into(),
        }
    }

    pub(crate) fn region_projections(
        &self,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> Vec<RegionProjection<'tcx, Self>> {
        let place = self.with_inherent_region(repacker);
        extract_regions(place.ty(repacker).ty, repacker)
            .iter()
            .map(|region| RegionProjection::new(*region, place, None, repacker).unwrap())
            .collect()
    }

    pub fn new<T: Into<SnapshotLocation>>(place: Place<'tcx>, at: Option<T>) -> Self {
        if let Some(at) = at {
            Self::OldPlace(PlaceSnapshot::new(place, at))
        } else {
            Self::Current { place }
        }
    }

    pub fn ty<C: Copy>(&self, repacker: CompilerCtxt<'_, 'tcx, C>) -> PlaceTy<'tcx> {
        self.place().ty(repacker)
    }

    pub(crate) fn project_deref(&self, repacker: CompilerCtxt<'_, 'tcx>) -> MaybeOldPlace<'tcx> {
        MaybeOldPlace::new(self.place().project_deref(repacker), self.location())
    }

    pub fn is_current(&self) -> bool {
        matches!(self, MaybeOldPlace::Current { .. })
    }

    pub fn to_json(&self, repacker: CompilerCtxt<'_, 'tcx>) -> serde_json::Value {
        json!({
            "place": self.place().to_json(repacker),
            "at": self.location().map(|loc| format!("{loc:?}")),
        })
    }
}

impl<'tcx> LabelPlace<'tcx> for MaybeOldPlace<'tcx> {
    fn label_place(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        latest: &Latest<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        match self {
            MaybeOldPlace::Current { place } => match predicate {
                LabelPlacePredicate::PrefixOrPostfix(p2) => {
                    if place.is_prefix(*p2) || p2.is_prefix(*place) {
                        *self = MaybeOldPlace::OldPlace(PlaceSnapshot::new(
                            *place,
                            latest.get(*place, ctxt),
                        ));
                        true
                    } else {
                        false
                    }
                }
            },
            _ => false,
        }
    }
}

impl<'tcx> HasPcgElems<Place<'tcx>> for MaybeOldPlace<'tcx> {
    fn pcg_elems(&mut self) -> Vec<&mut Place<'tcx>> {
        match self {
            MaybeOldPlace::Current { place } => vec![place],
            MaybeOldPlace::OldPlace(snapshot) => snapshot.pcg_elems(),
        }
    }
}
