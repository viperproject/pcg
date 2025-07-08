//! Data structures for lifetime projections.
use std::hash::Hash;
use std::{fmt, marker::PhantomData};

use derive_more::{Display, From, TryFrom};
use serde_json::json;

use super::has_pcs_elem::{HasPcgElems, LabelRegionProjection};
use super::{
    abstraction::node::AbstractionGraphNode, borrow_pcg_edge::LocalNode, visitor::extract_regions,
};
use crate::borrow_checker::BorrowCheckerInterface;
use crate::borrow_pcg::edge_data::LabelPlacePredicate;
use crate::borrow_pcg::has_pcs_elem::{LabelPlace, LabelRegionProjectionPredicate};
use crate::borrow_pcg::latest::Latest;
use crate::pcg::{PcgError, PcgInternalError};
use crate::pcg_validity_assert;
use crate::utils::json::ToJsonWithCompilerCtxt;
use crate::utils::place::maybe_old::MaybeOldPlace;
use crate::utils::place::maybe_remote::MaybeRemotePlace;
use crate::utils::remote::RemotePlace;
use crate::utils::{CompilerCtxt, SnapshotLocation};
use crate::{
    pcg::{LocalNodeLike, PCGNode, PCGNodeLike},
    rustc_interface::{
        index::{Idx, IndexVec},
        middle::{
            mir::{Const, Local, PlaceElem},
            ty::{
                self, DebruijnIndex, RegionVid, TyKind, TypeSuperVisitable, TypeVisitable,
                TypeVisitor,
            },
        },
    },
    utils::{display::DisplayWithCompilerCtxt, validity::HasValidityCheck, HasPlace, Place},
};

/// A region occuring in region projections
#[derive(PartialEq, Eq, Clone, Copy, Hash, From)]
pub enum PcgRegion {
    RegionVid(RegionVid),
    ReErased,
    ReStatic,
    ReBound(DebruijnIndex, ty::BoundRegion),
    ReLateParam(ty::LateParamRegion),
}

impl<'tcx> DisplayWithCompilerCtxt<'tcx, &dyn BorrowCheckerInterface<'tcx>> for RegionVid {
    fn to_short_string(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> String {
        if let Some(string) = ctxt.bc.override_region_debug_string(*self) {
            string.to_string()
        } else {
            format!("{self:?}")
        }
    }
}

impl std::fmt::Display for PcgRegion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_string(None))
    }
}

impl PcgRegion {
    pub fn to_string(&self, ctxt: Option<CompilerCtxt<'_, '_>>) -> String {
        match self {
            PcgRegion::RegionVid(vid) => {
                if let Some(ctxt) = ctxt {
                    vid.to_short_string(ctxt)
                } else {
                    format!("{vid:?}")
                }
            }
            PcgRegion::ReErased => "ReErased".to_string(),
            PcgRegion::ReStatic => "ReStatic".to_string(),
            PcgRegion::ReBound(debruijn_index, region) => {
                format!("ReBound({debruijn_index:?}, {region:?})")
            }
            PcgRegion::ReLateParam(_) => todo!(),
        }
    }

    pub fn vid(&self) -> Option<RegionVid> {
        match self {
            PcgRegion::RegionVid(vid) => Some(*vid),
            _ => None,
        }
    }
}

impl<'tcx, 'a> DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>> for PcgRegion {
    fn to_short_string(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    ) -> String {
        self.to_string(Some(ctxt))
    }
}

impl<'tcx> From<ty::Region<'tcx>> for PcgRegion {
    fn from(region: ty::Region<'tcx>) -> Self {
        match region.kind() {
            ty::RegionKind::ReVar(vid) => PcgRegion::RegionVid(vid),
            ty::RegionKind::ReErased => PcgRegion::ReErased,
            ty::RegionKind::ReEarlyParam(_) => todo!(),
            ty::RegionKind::ReBound(debruijn_index, inner) => {
                PcgRegion::ReBound(debruijn_index, inner)
            }
            ty::RegionKind::ReLateParam(late_param) => PcgRegion::ReLateParam(late_param),
            ty::RegionKind::ReStatic => PcgRegion::ReStatic,
            ty::RegionKind::RePlaceholder(_) => todo!(),
            ty::RegionKind::ReError(_) => todo!(),
        }
    }
}

/// The index of a region within a type.
///
/// For example is `a` has type `A<'t>` and `b` has type `B<'u>`,
/// an assignment e.g. `b = move a` will have region projections from `b`
/// to `u`
#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy, Ord, PartialOrd, From)]
pub struct RegionIdx(usize);

impl Idx for RegionIdx {
    fn new(idx: usize) -> Self {
        RegionIdx(idx)
    }

    fn index(self) -> usize {
        self.0
    }
}

/// The most general base of a lifetime projection. Either a [`MaybeRemotePlace`]
/// or a constant.
#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy, Display, From, TryFrom)]
pub enum MaybeRemoteRegionProjectionBase<'tcx> {
    Place(MaybeRemotePlace<'tcx>),
    Const(Const<'tcx>),
}

impl<'tcx> MaybeRemoteRegionProjectionBase<'tcx> {
    #[allow(unused)]
    pub(crate) fn is_mutable(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        match self {
            MaybeRemoteRegionProjectionBase::Place(p) => p.is_mutable(ctxt),
            MaybeRemoteRegionProjectionBase::Const(_) => false,
        }
    }
    pub(crate) fn base_ty<C: Copy>(self, ctxt: CompilerCtxt<'_, 'tcx, C>) -> ty::Ty<'tcx> {
        match self {
            MaybeRemoteRegionProjectionBase::Place(maybe_remote_place) => {
                let local_place: Place<'tcx> =
                    maybe_remote_place.related_local_place().local.into();
                local_place.ty(ctxt).ty
            }
            MaybeRemoteRegionProjectionBase::Const(c) => c.ty(),
        }
    }
    pub(crate) fn as_local_place_mut(&mut self) -> Option<&mut MaybeOldPlace<'tcx>> {
        match self {
            MaybeRemoteRegionProjectionBase::Place(p) => p.as_local_place_mut(),
            MaybeRemoteRegionProjectionBase::Const(_) => None,
        }
    }

    pub(crate) fn as_local_place(&self) -> Option<MaybeOldPlace<'tcx>> {
        match self {
            MaybeRemoteRegionProjectionBase::Place(p) => p.as_local_place(),
            MaybeRemoteRegionProjectionBase::Const(_) => None,
        }
    }
    pub(crate) fn as_current_place(&self) -> Option<Place<'tcx>> {
        match self {
            MaybeRemoteRegionProjectionBase::Place(p) => p.as_current_place(),
            MaybeRemoteRegionProjectionBase::Const(_) => None,
        }
    }
}
impl<'tcx> HasValidityCheck<'tcx> for MaybeRemoteRegionProjectionBase<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        match self {
            MaybeRemoteRegionProjectionBase::Place(p) => p.check_validity(ctxt),
            MaybeRemoteRegionProjectionBase::Const(_) => todo!(),
        }
    }
}

impl<'tcx, 'a> ToJsonWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>
    for MaybeRemoteRegionProjectionBase<'tcx>
{
    fn to_json(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    ) -> serde_json::Value {
        match self {
            MaybeRemoteRegionProjectionBase::Place(p) => p.to_json(ctxt),
            MaybeRemoteRegionProjectionBase::Const(_) => todo!(),
        }
    }
}

impl<'tcx, 'a> DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>
    for MaybeRemoteRegionProjectionBase<'tcx>
{
    fn to_short_string(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    ) -> String {
        match self {
            MaybeRemoteRegionProjectionBase::Place(p) => p.to_short_string(ctxt),
            MaybeRemoteRegionProjectionBase::Const(c) => format!("{c}"),
        }
    }
}

impl<'tcx> RegionProjectionBaseLike<'tcx> for MaybeRemoteRegionProjectionBase<'tcx> {
    fn to_maybe_remote_region_projection_base(&self) -> MaybeRemoteRegionProjectionBase<'tcx> {
        *self
    }

    fn regions<C: Copy>(
        &self,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> IndexVec<RegionIdx, PcgRegion> {
        match self {
            MaybeRemoteRegionProjectionBase::Place(p) => p.regions(repacker),
            MaybeRemoteRegionProjectionBase::Const(c) => extract_regions(c.ty(), repacker),
        }
    }
}

impl<'tcx, T: RegionProjectionBaseLike<'tcx>> PCGNodeLike<'tcx> for RegionProjection<'tcx, T> {
    fn to_pcg_node<C: Copy>(self, _ctxt: CompilerCtxt<'_, 'tcx, C>) -> PCGNode<'tcx> {
        self.with_base(self.base.to_maybe_remote_region_projection_base())
            .into()
    }
}

/// A lifetime projection label. A label can be either a [`SnapshotLocation`] or
/// a special "Placeholder" label.
///
/// If a lifetime projection is labelled with a location, it corresponds to the
/// memory of the projection at that point.
///
/// If it's labelled with the "Placeholder" label, it represents the memory that
/// the projection will refer to once it becomes accessible.
///
#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy, Ord, PartialOrd, From)]
pub enum RegionProjectionLabel {
    Location(SnapshotLocation),
    Placeholder,
}

impl std::fmt::Display for RegionProjectionLabel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RegionProjectionLabel::Location(location) => write!(f, "{}", location),
            RegionProjectionLabel::Placeholder => write!(f, "FUTURE"),
        }
    }
}

/// A lifetime projection b↓r, where `b` is a base and `r` is a region.
#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy, Ord, PartialOrd)]
pub struct RegionProjection<'tcx, P = MaybeRemoteRegionProjectionBase<'tcx>> {
    pub(crate) base: P,
    pub(crate) region_idx: RegionIdx,
    label: Option<RegionProjectionLabel>,
    phantom: PhantomData<&'tcx ()>,
}

impl<'tcx> LabelPlace<'tcx> for RegionProjection<'tcx> {
    fn label_place(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        latest: &Latest<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        if let Some(p) = self.base.as_local_place_mut() {
            p.label_place(predicate, latest, ctxt)
        } else {
            false
        }
    }
}

impl<P> RegionProjection<'_, P> {
    pub(crate) fn is_placeholder(&self) -> bool {
        self.label == Some(RegionProjectionLabel::Placeholder)
    }
    pub(crate) fn label(&self) -> Option<RegionProjectionLabel> {
        self.label
    }
}

impl<'tcx> From<RegionProjection<'tcx, Place<'tcx>>> for RegionProjection<'tcx> {
    fn from(rp: RegionProjection<'tcx, Place<'tcx>>) -> Self {
        RegionProjection {
            base: rp.base.into(),
            region_idx: rp.region_idx,
            label: rp.label,
            phantom: PhantomData,
        }
    }
}

impl<'tcx, T, P> TryFrom<PCGNode<'tcx, T, P>> for RegionProjection<'tcx, P> {
    type Error = ();
    fn try_from(node: PCGNode<'tcx, T, P>) -> Result<Self, Self::Error> {
        match node {
            PCGNode::RegionProjection(rp) => Ok(rp),
            _ => Err(()),
        }
    }
}

impl<'tcx, P: Eq + From<MaybeOldPlace<'tcx>>> LabelRegionProjection<'tcx>
    for RegionProjection<'tcx, P>
{
    fn label_region_projection(
        &mut self,
        predicate: &LabelRegionProjectionPredicate<'tcx>,
        label: Option<RegionProjectionLabel>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        match predicate {
            LabelRegionProjectionPredicate::Equals(region_projection) => {
                if self.region_idx == region_projection.region_idx
                    && self.base == region_projection.base.into()
                    && self.label == region_projection.label
                {
                    self.label = label;
                    true
                } else {
                    false
                }
            }
            LabelRegionProjectionPredicate::AllNonPlaceHolder(maybe_old_place, region_idx) => {
                if self.region_idx == *region_idx && self.base == (*maybe_old_place).into() {
                    self.label = label;
                    true
                } else {
                    false
                }
            }
        }
    }
}

impl<'tcx> From<RegionProjection<'tcx, MaybeOldPlace<'tcx>>>
    for RegionProjection<'tcx, MaybeRemotePlace<'tcx>>
{
    fn from(value: RegionProjection<'tcx, MaybeOldPlace<'tcx>>) -> Self {
        RegionProjection {
            base: value.base.into(),
            region_idx: value.region_idx,
            label: value.label,
            phantom: PhantomData,
        }
    }
}

struct TyVarianceVisitor<'mir, 'tcx> {
    ctxt: CompilerCtxt<'mir, 'tcx>,
    target: PcgRegion,
    found: bool,
}

impl<'tcx> TypeVisitor<ty::TyCtxt<'tcx>> for TyVarianceVisitor<'_, 'tcx> {
    fn visit_ty(&mut self, t: ty::Ty<'tcx>) {
        if self.found {
            return;
        }
        match t.kind() {
            TyKind::Adt(def_id, substs) => {
                let variances = self.ctxt.tcx().variances_of(def_id.did());
                for (idx, region) in substs.regions().enumerate() {
                    if self.target == region.into()
                        && variances.get(idx) == Some(&ty::Variance::Invariant)
                    {
                        self.found = true;
                    }
                }
            }
            TyKind::RawPtr(ty, mutbl) | TyKind::Ref(_, ty, mutbl) => {
                if mutbl.is_mut()
                    && extract_regions(*ty, self.ctxt)
                        .iter()
                        .any(|r| self.target == *r)
                {
                    self.found = true;
                }
                // Otherwise, this is an immutable reference, don't check under
                // here since nothing will be mutable
            }
            _ => {
                t.super_visit_with(self);
            }
        }
    }
}

impl<'tcx, T: RegionProjectionBaseLike<'tcx>> RegionProjection<'tcx, T> {
    pub(crate) fn can_be_labelled<BC: Copy>(&self, _ctxt: CompilerCtxt<'_, 'tcx, BC>) -> bool {
        true
    }
    pub(crate) fn is_invariant_in_type(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        let mut visitor = TyVarianceVisitor {
            ctxt,
            target: self.region(ctxt),
            found: false,
        };
        self.base
            .to_maybe_remote_region_projection_base()
            .base_ty(ctxt)
            .visit_with(&mut visitor);
        visitor.found
    }
}

impl<'tcx, T: RegionProjectionBaseLike<'tcx>> RegionProjection<'tcx, T> {
    #[must_use]
    pub(crate) fn unlabelled(self) -> RegionProjection<'tcx, T> {
        RegionProjection {
            base: self.base,
            region_idx: self.region_idx,
            label: None,
            phantom: PhantomData,
        }
    }
}
impl<'tcx, T: RegionProjectionBaseLike<'tcx>> RegionProjection<'tcx, T> {
    #[must_use]
    pub(crate) fn with_placeholder_label(
        self,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> RegionProjection<'tcx, T> {
        self.with_label(Some(RegionProjectionLabel::Placeholder), ctxt)
    }

    #[must_use]
    pub(crate) fn with_label<BC: Copy>(
        self,
        label: Option<RegionProjectionLabel>,
        ctxt: CompilerCtxt<'_, 'tcx, BC>,
    ) -> RegionProjection<'tcx, T> {
        if label.is_some() {
            pcg_validity_assert!(
                self.can_be_labelled(ctxt),
                "{:?} is not mutable and shouldn't be labelled",
                self,
            );
        }
        RegionProjection {
            base: self.base,
            region_idx: self.region_idx,
            label,
            phantom: PhantomData,
        }
    }
}
impl<'tcx> From<RegionProjection<'tcx, MaybeRemotePlace<'tcx>>> for RegionProjection<'tcx> {
    fn from(rp: RegionProjection<'tcx, MaybeRemotePlace<'tcx>>) -> Self {
        RegionProjection {
            base: rp.base.into(),
            region_idx: rp.region_idx,
            label: rp.label,
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
                label: rp.label,
                phantom: PhantomData,
            }),
            MaybeRemoteRegionProjectionBase::Const(_) => Err(()),
        }
    }
}

impl<'tcx> TryFrom<RegionProjection<'tcx>> for RegionProjection<'tcx, MaybeOldPlace<'tcx>> {
    type Error = String;
    fn try_from(rp: RegionProjection<'tcx>) -> Result<Self, Self::Error> {
        match rp.base {
            MaybeRemoteRegionProjectionBase::Place(p) => Ok(RegionProjection {
                base: p.try_into()?,
                region_idx: rp.region_idx,
                label: rp.label,
                phantom: PhantomData,
            }),
            MaybeRemoteRegionProjectionBase::Const(_) => {
                Err("Const cannot be converted to a region projection".to_string())
            }
        }
    }
}

impl<'tcx, P: RegionProjectionBaseLike<'tcx>> RegionProjection<'tcx, P> {
    pub fn base(&self) -> P {
        self.base
    }
}

impl<'tcx> LocalNodeLike<'tcx> for RegionProjection<'tcx, Place<'tcx>> {
    fn to_local_node<C: Copy>(self, _ctxt: CompilerCtxt<'_, 'tcx, C>) -> LocalNode<'tcx> {
        LocalNode::RegionProjection(self.with_base(MaybeOldPlace::Current { place: self.base }))
    }
}

impl<'tcx> LocalNodeLike<'tcx> for RegionProjection<'tcx, MaybeOldPlace<'tcx>> {
    fn to_local_node<C: Copy>(self, _repacker: CompilerCtxt<'_, 'tcx, C>) -> LocalNode<'tcx> {
        LocalNode::RegionProjection(self)
    }
}

/// Something that can be converted to a [`MaybeRemoteRegionProjectionBase`].
pub trait RegionProjectionBaseLike<'tcx>:
    Copy + std::fmt::Debug + std::hash::Hash + Eq + PartialEq
{
    fn regions<C: Copy>(
        &self,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> IndexVec<RegionIdx, PcgRegion>;

    fn to_maybe_remote_region_projection_base(&self) -> MaybeRemoteRegionProjectionBase<'tcx>;
}

impl<
        'tcx,
        'a,
        T: RegionProjectionBaseLike<'tcx>
            + DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    > DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>
    for RegionProjection<'tcx, T>
{
    fn to_short_string(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    ) -> String {
        let label_part = match self.label {
            Some(RegionProjectionLabel::Location(location)) => format!(" {location}"),
            Some(RegionProjectionLabel::Placeholder) => " FUTURE".to_string(),
            _ => "".to_string(),
        };
        format!(
            "{}↓{}{}",
            self.base.to_short_string(ctxt),
            self.region(ctxt).to_short_string(ctxt),
            label_part
        )
    }
}

impl<
        'tcx,
        'a,
        T: RegionProjectionBaseLike<'tcx>
            + ToJsonWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    > ToJsonWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>
    for RegionProjection<'tcx, T>
{
    fn to_json(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    ) -> serde_json::Value {
        json!({
            "place": self.base.to_json(ctxt),
            "region": self.region(ctxt).to_string(Some(ctxt)),
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
            label: rp.label,
            phantom: PhantomData,
        }
    }
}

impl<'tcx> HasPcgElems<MaybeOldPlace<'tcx>> for RegionProjection<'tcx, MaybeOldPlace<'tcx>> {
    fn pcg_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        vec![&mut self.base]
    }
}

impl<'tcx> TryFrom<AbstractionGraphNode<'tcx>> for RegionProjection<'tcx, MaybeOldPlace<'tcx>> {
    type Error = String;
    fn try_from(node: AbstractionGraphNode<'tcx>) -> Result<Self, Self::Error> {
        match *node {
            PCGNode::RegionProjection(rp) => rp.try_into(),
            PCGNode::Place(p) => Err(format!(
                "Place {:?} cannot be converted to a region projection",
                p
            )),
        }
    }
}

impl<'tcx> TryFrom<RegionProjection<'tcx, MaybeRemotePlace<'tcx>>>
    for RegionProjection<'tcx, MaybeOldPlace<'tcx>>
{
    type Error = String;
    fn try_from(rp: RegionProjection<'tcx, MaybeRemotePlace<'tcx>>) -> Result<Self, Self::Error> {
        Ok(RegionProjection {
            base: rp.base.try_into()?,
            region_idx: rp.region_idx,
            label: rp.label,
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
            label: rp.label,
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
            label: rp.label,
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

    fn project_deeper<C: Copy>(
        &self,
        elem: PlaceElem<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> Result<Self, PcgError>
    where
        Self: Clone + HasValidityCheck<'tcx>,
    {
        RegionProjection::new(
            self.region(repacker),
            self.base.project_deeper(elem, repacker)?,
            self.label,
            repacker,
        )
        .map_err(|e| e.into())
    }

    fn iter_projections<C: Copy>(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, C>,
    ) -> Vec<(Self, PlaceElem<'tcx>)> {
        self.base
            .iter_projections(ctxt)
            .into_iter()
            .map(move |(base, elem)| {
                (
                    RegionProjection::new(self.region(ctxt), base, self.label, ctxt)
                        .unwrap_or_else(|e| {
                            panic!(
                                "Error iter projections for {:?}: {:?}. Place ty: {:?}",
                                self,
                                e,
                                base.place().ty(ctxt),
                            );
                        }),
                    elem,
                )
            })
            .collect()
    }
}

impl<'tcx, T: RegionProjectionBaseLike<'tcx>> HasValidityCheck<'tcx> for RegionProjection<'tcx, T> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        let num_regions = self.base.regions(ctxt);
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
    pub(crate) fn new<C: Copy>(
        region: PcgRegion,
        base: T,
        label: Option<RegionProjectionLabel>,
        ctxt: CompilerCtxt<'_, 'tcx, C>,
    ) -> Result<Self, PcgInternalError> {
        let region_idx = base
            .regions(ctxt)
            .into_iter_enumerated()
            .find(|(_, r)| *r == region)
            .map(|(idx, _)| idx);
        let region_idx = match region_idx {
            Some(region_idx) => region_idx,
            None => {
                return Err(PcgInternalError::new(format!(
                    "Region {region} not found in place {base:?}"
                )));
            }
        };

        let result = Self {
            base,
            region_idx,
            label,
            phantom: PhantomData,
        };
        Ok(result)
    }

    pub(crate) fn region<C: Copy>(&self, ctxt: CompilerCtxt<'_, 'tcx, C>) -> PcgRegion {
        let regions = self.base.regions(ctxt);
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
    ) -> RegionProjection<'tcx, U> {
        RegionProjection {
            base,
            region_idx: self.region_idx,
            label: self.label,
            phantom: PhantomData,
        }
    }
}

impl<'tcx> RegionProjection<'tcx, MaybeOldPlace<'tcx>> {
    /// If the region projection is of the form `x↓'a` and `x` has type `&'a T` or `&'a mut T`,
    /// this returns `*x`.
    pub fn deref(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Option<MaybeOldPlace<'tcx>> {
        if self.base.ty_region(ctxt) == Some(self.region(ctxt)) {
            Some(self.base.project_deref(ctxt))
        } else {
            None
        }
    }
}

pub(crate) type LocalRegionProjection<'tcx> = RegionProjection<'tcx, MaybeOldPlace<'tcx>>;

impl<'tcx> LocalRegionProjection<'tcx> {
    pub fn to_region_projection(&self) -> RegionProjection<'tcx> {
        self.with_base(self.base.into())
    }
    pub(crate) fn related_local(&self) -> Local {
        self.base.local()
    }
}

impl<'tcx> RegionProjection<'tcx> {
    pub fn local(&self) -> Option<Local> {
        self.base.as_local_place().map(|p| p.local())
    }

    pub(crate) fn is_remote(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        self.as_local_region_projection().is_none()
    }

    fn as_local_region_projection(&self) -> Option<RegionProjection<'tcx, MaybeOldPlace<'tcx>>> {
        match self.base {
            MaybeRemoteRegionProjectionBase::Place(maybe_remote_place) => {
                match maybe_remote_place {
                    MaybeRemotePlace::Local(local) => Some(self.with_base(local)),
                    _ => None,
                }
            }
            MaybeRemoteRegionProjectionBase::Const(_) => None,
        }
    }

    /// If the region projection is of the form `x↓'a` and `x` has type `&'a T` or `&'a mut T`,
    /// this returns `*x`. Otherwise, it returns `None`.
    pub fn deref(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Option<MaybeOldPlace<'tcx>> {
        self.as_local_region_projection()
            .and_then(|rp| rp.deref(ctxt))
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
