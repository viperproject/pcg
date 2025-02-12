use std::{fmt, marker::PhantomData};

use derive_more::{Display, From, TryFrom};
use serde_json::json;

use crate::{
    combined_pcs::{LocalNodeLike, PCGNode, PCGNodeLike},
    rustc_interface::{
        ast::Mutability,
        data_structures::fx::FxHashSet,
        index::{Idx, IndexVec},
        middle::{
            mir::{Const, Local, PlaceElem},
            ty::{self, DebruijnIndex, RegionVid},
        },
    },
    utils::{display::DisplayWithRepacker, validity::HasValidityCheck, HasPlace, Place},
};
use crate::utils::json::ToJsonWithRepacker;
use crate::utils::place::maybe_old::MaybeOldPlace;
use crate::utils::place::maybe_remote::MaybeRemotePlace;
use crate::utils::PlaceRepacker;
use crate::utils::remote::RemotePlace;
use super::{
    borrow_pcg_edge::LocalNode,
    borrows_visitor::extract_regions,
    coupling_graph_constructor::CGNode,
};
use super::has_pcs_elem::HasPcsElems;

/// A region occuring in region projections
#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub enum PCGRegion {
    RegionVid(RegionVid),
    ReErased,
    ReStatic,
    ReBound(DebruijnIndex, ty::BoundRegion),

    ReLateParam(ty::LateParamRegion),

    /// A placeholder for if an internal error occured, only used for debugging
    PCGInternalErr,
}

impl<'tcx> std::fmt::Display for PCGRegion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PCGRegion::RegionVid(vid) => write!(f, "{:?}", vid),
            PCGRegion::ReErased => write!(f, "ReErased"),
            PCGRegion::ReStatic => write!(f, "ReStatic"),
            PCGRegion::ReBound(debruijn_index, region) => {
                write!(f, "ReBound({:?}, {:?})", debruijn_index, region)
            }
            PCGRegion::PCGInternalErr => write!(f, "ERR"),
            PCGRegion::ReLateParam(_) => todo!(),
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
            ty::RegionKind::ReLateParam(late_param) => PCGRegion::ReLateParam(late_param),
            ty::RegionKind::ReStatic => PCGRegion::ReStatic,
            ty::RegionKind::RePlaceholder(_) => todo!(),
            ty::RegionKind::ReError(_) => todo!(),
        }
    }
}

/// The index of a region within a type. We store the index instead of the
/// region itself to appropriately maintain the same relative region for
/// handling moves.
///
/// For example is `a` has type `A<'t>` and `b` has type `B<'u>`,
/// an assignment e.g. `b = move a` will have region projections from `b`
/// to `u`
#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy, Ord, PartialOrd)]
pub struct RegionIdx(usize);

impl Idx for RegionIdx {
    fn new(idx: usize) -> Self {
        RegionIdx(idx)
    }

    fn index(self) -> usize {
        self.0
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy, Display, From, TryFrom)]
pub enum MaybeRemoteRegionProjectionBase<'tcx> {
    Place(MaybeRemotePlace<'tcx>),
    Const(Const<'tcx>),
}

impl<'tcx> MaybeRemoteRegionProjectionBase<'tcx> {
    pub(crate) fn is_old(&self) -> bool {
        match self {
            MaybeRemoteRegionProjectionBase::Place(p) => p.is_old(),
            MaybeRemoteRegionProjectionBase::Const(_) => false,
        }
    }

    pub(crate) fn as_local_place(&self) -> Option<MaybeOldPlace<'tcx>> {
        match self {
            MaybeRemoteRegionProjectionBase::Place(p) => p.as_local_place(),
            MaybeRemoteRegionProjectionBase::Const(_) => None,
        }
    }
}
impl<'tcx> HasValidityCheck<'tcx> for MaybeRemoteRegionProjectionBase<'tcx> {
    fn check_validity(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Result<(), String> {
        match self {
            MaybeRemoteRegionProjectionBase::Place(p) => p.check_validity(repacker),
            MaybeRemoteRegionProjectionBase::Const(_) => todo!(),
        }
    }
}

impl<'tcx> ToJsonWithRepacker<'tcx> for MaybeRemoteRegionProjectionBase<'tcx> {
    fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        match self {
            MaybeRemoteRegionProjectionBase::Place(p) => p.to_json(repacker),
            MaybeRemoteRegionProjectionBase::Const(_) => todo!(),
        }
    }
}

impl<'tcx> DisplayWithRepacker<'tcx> for MaybeRemoteRegionProjectionBase<'tcx> {
    fn to_short_string(&self, repacker: PlaceRepacker<'_, 'tcx>) -> String {
        match self {
            MaybeRemoteRegionProjectionBase::Place(p) => p.to_short_string(repacker),
            MaybeRemoteRegionProjectionBase::Const(c) => format!("{}", c),
        }
    }
}

impl<'tcx> RegionProjectionBaseLike<'tcx> for MaybeRemoteRegionProjectionBase<'tcx> {
    fn regions(&self, repacker: PlaceRepacker<'_, 'tcx>) -> IndexVec<RegionIdx, PCGRegion> {
        match self {
            MaybeRemoteRegionProjectionBase::Place(p) => p.regions(repacker),
            MaybeRemoteRegionProjectionBase::Const(c) => {
                let ty = c.ty();
                extract_regions(ty)
            }
        }
    }

    fn to_maybe_remote_region_projection_base(&self) -> MaybeRemoteRegionProjectionBase<'tcx> {
        *self
    }
}

impl<'tcx, T: RegionProjectionBaseLike<'tcx>> PCGNodeLike<'tcx> for RegionProjection<'tcx, T> {
    fn to_pcg_node(self) -> PCGNode<'tcx> {
        self.map_base(|base| base.to_maybe_remote_region_projection_base())
            .into()
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy, Ord, PartialOrd)]
pub struct RegionProjection<'tcx, P = MaybeRemoteRegionProjectionBase<'tcx>> {
    base: P,
    region_idx: RegionIdx,
    phantom: PhantomData<&'tcx ()>,
}

impl<'tcx, P: RegionProjectionBaseLike<'tcx>> RegionProjection<'tcx, P> {
    pub(crate) fn base(&self) -> P {
        self.base
    }
}

impl<'tcx> LocalNodeLike<'tcx> for RegionProjection<'tcx, Place<'tcx>> {
    fn to_local_node(self) -> LocalNode<'tcx> {
        LocalNode::RegionProjection(self.map_base(|base| MaybeOldPlace::Current { place: base }))
    }
}

impl<'tcx> LocalNodeLike<'tcx> for RegionProjection<'tcx, MaybeOldPlace<'tcx>> {
    fn to_local_node(self) -> LocalNode<'tcx> {
        LocalNode::RegionProjection(self)
    }
}

pub trait RegionProjectionBaseLike<'tcx>:
    Copy
    + std::fmt::Debug
    + std::hash::Hash
    + Eq
    + PartialEq
    + ToJsonWithRepacker<'tcx>
    + DisplayWithRepacker<'tcx>
{
    fn regions(&self, repacker: PlaceRepacker<'_, 'tcx>) -> IndexVec<RegionIdx, PCGRegion>;

    fn to_maybe_remote_region_projection_base(&self) -> MaybeRemoteRegionProjectionBase<'tcx>;
}

impl<'tcx, T: RegionProjectionBaseLike<'tcx>> DisplayWithRepacker<'tcx>
    for RegionProjection<'tcx, T>
{
    fn to_short_string(&self, repacker: PlaceRepacker<'_, 'tcx>) -> String {
        format!(
            "{}↓{}",
            self.base.to_short_string(repacker),
            self.region(repacker)
        )
    }
}

impl<'tcx, T: RegionProjectionBaseLike<'tcx>> ToJsonWithRepacker<'tcx>
    for RegionProjection<'tcx, T>
{
    fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        json!({
            "place": self.base.to_json(repacker),
            "region": self.region(repacker).to_string(),
        })
    }
}

impl<'tcx, T: std::fmt::Display> fmt::Display for RegionProjection<'tcx, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}↓{:?}", self.base, self.region_idx)
    }
}

impl<'tcx> From<RegionProjection<'tcx, Place<'tcx>>>
    for RegionProjection<'tcx, MaybeRemotePlace<'tcx>>
{
    fn from(rp: RegionProjection<'tcx, Place<'tcx>>) -> Self {
        RegionProjection {
            base: rp.base.into(),
            region_idx: rp.region_idx,
            phantom: PhantomData,
        }
    }
}

impl<'tcx> HasPcsElems<MaybeOldPlace<'tcx>> for RegionProjection<'tcx, MaybeOldPlace<'tcx>> {
    fn pcs_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        vec![&mut self.base]
    }
}

impl<'tcx> TryFrom<CGNode<'tcx>> for RegionProjection<'tcx, MaybeOldPlace<'tcx>> {
    type Error = ();
    fn try_from(node: CGNode<'tcx>) -> Result<Self, Self::Error> {
        match node {
            CGNode::RegionProjection(rp) => rp.try_into(),
            CGNode::RemotePlace(_) => Err(()),
        }
    }
}

impl<'tcx> TryFrom<RegionProjection<'tcx, MaybeRemotePlace<'tcx>>>
    for RegionProjection<'tcx, MaybeOldPlace<'tcx>>
{
    type Error = ();
    fn try_from(rp: RegionProjection<'tcx, MaybeRemotePlace<'tcx>>) -> Result<Self, Self::Error> {
        Ok(RegionProjection {
            base: rp.base.try_into()?,
            region_idx: rp.region_idx,
            phantom: PhantomData,
        })
    }
}

impl<'tcx> From<MaybeOldPlace<'tcx>> for MaybeRemoteRegionProjectionBase<'tcx> {
    fn from(place: MaybeOldPlace<'tcx>) -> Self {
        MaybeRemoteRegionProjectionBase::Place(place.into())
    }
}

impl<'tcx> From<RegionProjection<'tcx, MaybeOldPlace<'tcx>>> for RegionProjection<'tcx> {
    fn from(rp: RegionProjection<'tcx, MaybeOldPlace<'tcx>>) -> Self {
        RegionProjection {
            base: rp.base.into(),
            region_idx: rp.region_idx,
            phantom: PhantomData,
        }
    }
}

impl<'tcx> From<RegionProjection<'tcx, Place<'tcx>>>
    for RegionProjection<'tcx, MaybeOldPlace<'tcx>>
{
    fn from(rp: RegionProjection<'tcx, Place<'tcx>>) -> Self {
        RegionProjection {
            base: rp.base.into(),
            region_idx: rp.region_idx,
            phantom: PhantomData,
        }
    }
}

impl<'tcx, T: RegionProjectionBaseLike<'tcx> + HasPlace<'tcx>> HasPlace<'tcx>
    for RegionProjection<'tcx, T>
{
    fn place(&self) -> Place<'tcx> {
        self.base.place()
    }

    fn place_mut(&mut self) -> &mut Place<'tcx> {
        self.base.place_mut()
    }

    fn project_deeper(&self, repacker: PlaceRepacker<'_, 'tcx>, elem: PlaceElem<'tcx>) -> Self
    where
        Self: Clone + HasValidityCheck<'tcx>,
    {
        RegionProjection::new(
            self.region(repacker),
            self.base.project_deeper(repacker, elem),
            repacker,
        )
    }
}

impl<'tcx, T: RegionProjectionBaseLike<'tcx>> HasValidityCheck<'tcx> for RegionProjection<'tcx, T> {
    fn check_validity(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Result<(), String> {
        let num_regions = self.base.regions(repacker);
        if self.region_idx.index() >= num_regions.len() {
            Err(format!(
                "Region index {} is out of bounds for place {:?}",
                self.region_idx.index(),
                self.base
            ))
        } else {
            Ok(())
        }
    }
}

impl<'tcx, T: RegionProjectionBaseLike<'tcx>> RegionProjection<'tcx, T> {
    pub(crate) fn new(region: PCGRegion, base: T, repacker: PlaceRepacker<'_, 'tcx>) -> Self {
        let region_idx = base
            .regions(repacker)
            .into_iter_enumerated()
            .find(|(_, r)| *r == region)
            .map(|(idx, _)| idx)
            .unwrap_or_else(|| panic!("Region {} not found in place {:?}", region, base));
        let result = Self {
            base,
            region_idx,
            phantom: PhantomData,
        };
        if cfg!(debug_assertions) {
            result.assert_validity(repacker);
        }
        result
    }

    pub(crate) fn region(&self, repacker: PlaceRepacker<'_, 'tcx>) -> PCGRegion {
        let regions = self.base.regions(repacker);
        if self.region_idx.index() >= regions.len() {
            PCGRegion::PCGInternalErr
        } else {
            regions[self.region_idx]
        }
    }
}

impl<'tcx, T: Copy> RegionProjection<'tcx, T> {
    pub(crate) fn place(&self) -> T {
        self.base
    }
}

impl<'tcx, T> RegionProjection<'tcx, T> {
    pub(crate) fn place_mut(&mut self) -> &mut T {
        &mut self.base
    }

    pub(crate) fn map_base<U>(self, f: impl FnOnce(T) -> U) -> RegionProjection<'tcx, U> {
        RegionProjection {
            base: f(self.base),
            region_idx: self.region_idx,
            phantom: PhantomData,
        }
    }
}

impl<'tcx> RegionProjection<'tcx, MaybeOldPlace<'tcx>> {
    /// If the region projection is of the form `x↓'a` and `x` has type `&'a T` or `&'a mut T`,
    /// this returns `*x`.
    pub fn deref(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Option<MaybeOldPlace<'tcx>> {
        if self.base.ty_region(repacker) == Some(self.region(repacker)) {
            Some(self.base.project_deref(repacker))
        } else {
            None
        }
    }
}

impl<'tcx> RegionProjection<'tcx> {
    pub fn local(&self) -> Option<Local> {
        self.base.as_local_place().map(|p| p.local())
    }

    /// Returns `true` iff the place is a mutable reference, or if the place is
    /// a mutable struct. If the place is a remote place, it is mutable iff the
    /// corresponding input argument is a mutable reference.
    pub(crate) fn mutability(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Mutability {
        let place = match self.base {
            MaybeRemoteRegionProjectionBase::Place(p) => p.related_local_place(),
            MaybeRemoteRegionProjectionBase::Const(_) => {
                return Mutability::Not;
            }
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

    fn as_local_region_projection(&self) -> Option<RegionProjection<'tcx, MaybeOldPlace<'tcx>>> {
        match self.base {
            MaybeRemoteRegionProjectionBase::Place(maybe_remote_place) => {
                match maybe_remote_place {
                    MaybeRemotePlace::Local(local) => Some(self.map_base(|_| local)),
                    _ => None,
                }
            }
            MaybeRemoteRegionProjectionBase::Const(_) => None,
        }
    }

    /// If the region projection is of the form `x↓'a` and `x` has type `&'a T` or `&'a mut T`,
    /// this returns `*x`. Otherwise, it returns `None`.
    pub fn deref(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Option<MaybeOldPlace<'tcx>> {
        self.as_local_region_projection()
            .and_then(|rp| rp.deref(repacker))
    }

    /// Returns the set of pairs (srp, drp) where srp ∈
    /// `source.region_projections(repacker)` and drp ∈
    /// `dest.region_projections(repacker)` and `srp.region() == drp.region()`.
    pub(crate) fn connections_between_places(
        source: MaybeOldPlace<'tcx>,
        dest: MaybeOldPlace<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> FxHashSet<(
        RegionProjection<'tcx, MaybeOldPlace<'tcx>>,
        RegionProjection<'tcx, MaybeOldPlace<'tcx>>,
    )> {
        let mut edges = FxHashSet::default();
        for rp in source.region_projections(repacker) {
            for erp in dest.region_projections(repacker) {
                if rp.region(repacker) == erp.region(repacker) {
                    edges.insert((rp, erp));
                }
            }
        }
        edges
    }
}

impl<'tcx> HasPcsElems<MaybeOldPlace<'tcx>> for RegionProjection<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        self.base.pcs_elems()
    }
}

impl<'tcx> HasPcsElems<MaybeOldPlace<'tcx>> for MaybeRemoteRegionProjectionBase<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        match self {
            MaybeRemoteRegionProjectionBase::Place(p) => p.pcs_elems(),
            MaybeRemoteRegionProjectionBase::Const(_) => vec![],
        }
    }
}

impl<'tcx> From<RemotePlace> for MaybeRemoteRegionProjectionBase<'tcx> {
    fn from(remote_place: RemotePlace) -> Self {
        MaybeRemoteRegionProjectionBase::Place(remote_place.into())
    }
}