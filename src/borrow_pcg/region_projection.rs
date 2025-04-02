use std::hash::Hash;
use std::{fmt, marker::PhantomData};

use derive_more::{Display, From, TryFrom};
use serde_json::json;

use super::has_pcs_elem::HasPcgElems;
use super::{
    borrow_pcg_edge::LocalNode, coupling_graph_constructor::CGNode, visitor::extract_regions,
};
use crate::pcg::{PCGInternalError, PcgError};
use crate::utils::json::ToJsonWithRepacker;
use crate::utils::place::maybe_old::MaybeOldPlace;
use crate::utils::place::maybe_remote::MaybeRemotePlace;
use crate::utils::remote::RemotePlace;
use crate::utils::{PlaceRepacker, SnapshotLocation};
use crate::validity_checks_enabled;
use crate::{
    pcg::{LocalNodeLike, PCGNode, PCGNodeLike},
    rustc_interface::{
        index::{Idx, IndexVec},
        middle::{
            mir::{Const, Local, PlaceElem},
            ty::{self, DebruijnIndex, RegionVid},
        },
    },
    utils::{display::DisplayWithRepacker, validity::HasValidityCheck, HasPlace, Place},
};

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

impl std::fmt::Display for PCGRegion {
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
    fn to_maybe_remote_region_projection_base(&self) -> MaybeRemoteRegionProjectionBase<'tcx> {
        *self
    }

    fn regions(&self, repacker: PlaceRepacker<'_, 'tcx>) -> IndexVec<RegionIdx, PCGRegion> {
        match self {
            MaybeRemoteRegionProjectionBase::Place(p) => p.regions(repacker),
            MaybeRemoteRegionProjectionBase::Const(c) => extract_regions(c.ty(), repacker),
        }
    }
}

impl<'tcx, T: RegionProjectionBaseLike<'tcx>> PCGNodeLike<'tcx> for RegionProjection<'tcx, T> {
    fn to_pcg_node(self, repacker: PlaceRepacker<'_, 'tcx>) -> PCGNode<'tcx> {
        self.with_base(self.base.to_maybe_remote_region_projection_base(), repacker)
            .into()
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy, Ord, PartialOrd)]
pub struct RegionProjection<'tcx, P = MaybeRemoteRegionProjectionBase<'tcx>> {
    pub(crate) base: P,
    pub(crate) region_idx: RegionIdx,
    pub(crate) location: Option<SnapshotLocation>,
    phantom: PhantomData<&'tcx ()>,
}

impl<'tcx> From<RegionProjection<'tcx, MaybeOldPlace<'tcx>>>
    for RegionProjection<'tcx, MaybeRemotePlace<'tcx>>
{
    fn from(value: RegionProjection<'tcx, MaybeOldPlace<'tcx>>) -> Self {
        RegionProjection {
            base: value.base.into(),
            region_idx: value.region_idx,
            location: value.location,
            phantom: PhantomData,
        }
    }
}

impl<'tcx> RegionProjection<'tcx, MaybeOldPlace<'tcx>> {
    pub(crate) fn label_place(
        self,
        location: SnapshotLocation,
    ) -> RegionProjection<'tcx, MaybeOldPlace<'tcx>> {
        RegionProjection {
            base: self.base.with_location(location),
            region_idx: self.region_idx,
            location: self.location,
            phantom: PhantomData,
        }
    }
}
impl<'tcx> From<RegionProjection<'tcx, MaybeRemotePlace<'tcx>>> for RegionProjection<'tcx> {
    fn from(rp: RegionProjection<'tcx, MaybeRemotePlace<'tcx>>) -> Self {
        RegionProjection {
            base: rp.base.into(),
            region_idx: rp.region_idx,
            location: rp.location,
            phantom: PhantomData,
        }
    }
}

impl<'tcx> TryFrom<RegionProjection<'tcx>> for RegionProjection<'tcx, MaybeRemotePlace<'tcx>> {
    type Error = ();
    fn try_from(rp: RegionProjection<'tcx>) -> Result<Self, Self::Error> {
        match rp.base {
            MaybeRemoteRegionProjectionBase::Place(p) => Ok(RegionProjection {
                base: p,
                region_idx: rp.region_idx,
                location: rp.location,
                phantom: PhantomData,
            }),
            MaybeRemoteRegionProjectionBase::Const(_) => Err(()),
        }
    }
}

impl<'tcx> TryFrom<RegionProjection<'tcx>> for RegionProjection<'tcx, MaybeOldPlace<'tcx>> {
    type Error = ();
    fn try_from(rp: RegionProjection<'tcx>) -> Result<Self, Self::Error> {
        match rp.base {
            MaybeRemoteRegionProjectionBase::Place(p) => Ok(RegionProjection {
                base: p.try_into()?,
                region_idx: rp.region_idx,
                location: rp.location,
                phantom: PhantomData,
            }),
            MaybeRemoteRegionProjectionBase::Const(_) => Err(()),
        }
    }
}

impl<'tcx, P: RegionProjectionBaseLike<'tcx>> RegionProjection<'tcx, P> {
    pub(crate) fn base(&self) -> P {
        self.base
    }
}

impl<'tcx> LocalNodeLike<'tcx> for RegionProjection<'tcx, Place<'tcx>> {
    fn to_local_node(self, repacker: PlaceRepacker<'_, 'tcx>) -> LocalNode<'tcx> {
        LocalNode::RegionProjection(
            self.with_base(MaybeOldPlace::Current { place: self.base }, repacker),
        )
    }
}

impl<'tcx> LocalNodeLike<'tcx> for RegionProjection<'tcx, MaybeOldPlace<'tcx>> {
    fn to_local_node(self, _repacker: PlaceRepacker<'_, 'tcx>) -> LocalNode<'tcx> {
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

impl<T: std::fmt::Display> fmt::Display for RegionProjection<'_, T> {
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
            location: rp.location,
            phantom: PhantomData,
        }
    }
}

impl<'tcx> HasPcgElems<MaybeOldPlace<'tcx>> for RegionProjection<'tcx, MaybeOldPlace<'tcx>> {
    fn pcg_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        vec![&mut self.base]
    }
}

impl<'tcx> TryFrom<CGNode<'tcx>> for RegionProjection<'tcx, MaybeOldPlace<'tcx>> {
    type Error = ();
    fn try_from(node: CGNode<'tcx>) -> Result<Self, Self::Error> {
        match node {
            CGNode::RegionProjection(rp) => rp.try_into(),
            CGNode::Place(_) => Err(()),
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
            location: rp.location,
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
            location: rp.location,
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
            location: rp.location,
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

    fn project_deeper(
        &self,
        elem: PlaceElem<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Result<Self, PcgError>
    where
        Self: Clone + HasValidityCheck<'tcx>,
    {
        RegionProjection::new(
            self.region(repacker),
            self.base.project_deeper(elem, repacker)?,
            repacker,
        )
        .map_err(|e| e.into())
    }

    fn iter_projections(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Vec<(Self, PlaceElem<'tcx>)> {
        self.assert_validity(repacker); // DEBUG: Something's wrong if this fails here
        self.base
            .iter_projections(repacker)
            .into_iter()
            .map(move |(base, elem)| {
                (
                    RegionProjection::new(self.region(repacker), base, repacker).unwrap_or_else(
                        |e| {
                            panic!(
                                "Error iter projections for {}: {:?}. Place ty: {:?}",
                                self.to_short_string(repacker),
                                e,
                                base.place().ty(repacker),
                            );
                        },
                    ),
                    elem,
                )
            })
            .collect()
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
    pub(crate) fn new(
        region: PCGRegion,
        base: T,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Result<Self, PCGInternalError> {
        let region_idx = base
            .regions(repacker)
            .into_iter_enumerated()
            .find(|(_, r)| *r == region)
            .map(|(idx, _)| idx);
        let region_idx = match region_idx {
            Some(region_idx) => region_idx,
            None => {
                return Err(PCGInternalError::new(format!(
                    "Region {} not found in place {:?}",
                    region, base
                )));
            }
        };
        let result = Self {
            base,
            region_idx,
            location: None,
            phantom: PhantomData,
        };
        if validity_checks_enabled() {
            result.assert_validity(repacker);
        }
        Ok(result)
    }

    pub(crate) fn region(&self, repacker: PlaceRepacker<'_, 'tcx>) -> PCGRegion {
        let regions = self.base.regions(repacker);
        if self.region_idx.index() >= regions.len() {
            unreachable!()
        } else {
            regions[self.region_idx]
        }
    }
}

impl<T: Copy> RegionProjection<'_, T> {
    pub fn place(&self) -> T {
        self.base
    }
}

impl<'tcx, T> RegionProjection<'tcx, T> {
    pub(crate) fn place_mut(&mut self) -> &mut T {
        &mut self.base
    }

    pub(crate) fn with_base<U: RegionProjectionBaseLike<'tcx>>(
        self,
        base: U,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> RegionProjection<'tcx, U> {
        let result = RegionProjection {
            base,
            region_idx: self.region_idx,
            location: self.location,
            phantom: PhantomData,
        };
        result.assert_validity(repacker);
        result
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

pub(crate) type LocalRegionProjection<'tcx> = RegionProjection<'tcx, MaybeOldPlace<'tcx>>;

impl<'tcx> LocalRegionProjection<'tcx> {
    pub fn to_region_projection(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> RegionProjection<'tcx> {
        self.with_base(self.base.into(), repacker)
    }
}

impl<'tcx> RegionProjection<'tcx> {
    pub fn local(&self) -> Option<Local> {
        self.base.as_local_place().map(|p| p.local())
    }

    fn as_local_region_projection(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Option<RegionProjection<'tcx, MaybeOldPlace<'tcx>>> {
        match self.base {
            MaybeRemoteRegionProjectionBase::Place(maybe_remote_place) => {
                match maybe_remote_place {
                    MaybeRemotePlace::Local(local) => Some(self.with_base(local, repacker)),
                    _ => None,
                }
            }
            MaybeRemoteRegionProjectionBase::Const(_) => None,
        }
    }

    /// If the region projection is of the form `x↓'a` and `x` has type `&'a T` or `&'a mut T`,
    /// this returns `*x`. Otherwise, it returns `None`.
    pub fn deref(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Option<MaybeOldPlace<'tcx>> {
        self.as_local_region_projection(repacker)
            .and_then(|rp| rp.deref(repacker))
    }
}

impl<'tcx> HasPcgElems<MaybeOldPlace<'tcx>> for RegionProjection<'tcx> {
    fn pcg_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        self.base.pcg_elems()
    }
}

impl<'tcx> HasPcgElems<MaybeOldPlace<'tcx>> for MaybeRemoteRegionProjectionBase<'tcx> {
    fn pcg_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        match self {
            MaybeRemoteRegionProjectionBase::Place(p) => p.pcg_elems(),
            MaybeRemoteRegionProjectionBase::Const(_) => vec![],
        }
    }
}

impl From<RemotePlace> for MaybeRemoteRegionProjectionBase<'_> {
    fn from(remote_place: RemotePlace) -> Self {
        MaybeRemoteRegionProjectionBase::Place(remote_place.into())
    }
}
