//! Data structures for lifetime projections.
use std::hash::Hash;
use std::{fmt, marker::PhantomData};

use derive_more::{Display, From, TryFrom};
use serde_json::json;

use super::has_pcs_elem::LabelLifetimeProjection;
use super::{
    abstraction::node::AbstractionGraphNode, borrow_pcg_edge::LocalNode, visitor::extract_regions,
};
use crate::borrow_checker::BorrowCheckerInterface;
use crate::borrow_pcg::edge_data::LabelPlacePredicate;
use crate::borrow_pcg::graph::loop_abstraction::MaybeRemoteCurrentPlace;
use crate::borrow_pcg::has_pcs_elem::{
    LabelLifetimeProjectionPredicate, LabelLifetimeProjectionResult, LabelNodeContext,
    LabelPlaceWithContext, PlaceLabeller,
};
use crate::error::{PcgError, PcgInternalError};
use crate::utils::json::ToJsonWithCompilerCtxt;
use crate::utils::place::maybe_old::MaybeLabelledPlace;
use crate::utils::place::maybe_remote::MaybeRemotePlace;
use crate::utils::remote::RemotePlace;
use crate::utils::{CompilerCtxt, HasBorrowCheckerCtxt, HasCompilerCtxt, SnapshotLocation};
use crate::{
    pcg::{LocalNodeLike, PCGNodeLike, PcgNode},
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
    utils::{HasPlace, Place, display::DisplayWithCompilerCtxt, validity::HasValidityCheck},
};

/// A region occuring in region projections
#[derive(PartialEq, Eq, Clone, Copy, Hash, From, Debug)]
pub enum PcgRegion {
    RegionVid(RegionVid),
    ReErased,
    ReStatic,
    ReBound(DebruijnIndex, ty::BoundRegion),
    ReLateParam(ty::LateParamRegion),
}

impl<'tcx> DisplayWithCompilerCtxt<'tcx, &dyn BorrowCheckerInterface<'tcx>> for RegionVid {
    fn to_short_string(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, &dyn BorrowCheckerInterface<'tcx>>,
    ) -> String {
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
    pub(crate) fn maybe_remote_current_place(&self) -> Option<MaybeRemoteCurrentPlace<'tcx>> {
        match self {
            MaybeRemoteRegionProjectionBase::Place(p) => p.maybe_remote_current_place(),
            MaybeRemoteRegionProjectionBase::Const(_) => None,
        }
    }
    pub(crate) fn is_mutable<'a>(&self, ctxt: impl HasCompilerCtxt<'a, 'tcx>) -> bool
    where
        'tcx: 'a,
    {
        match self {
            MaybeRemoteRegionProjectionBase::Place(p) => p.is_mutable(ctxt),
            MaybeRemoteRegionProjectionBase::Const(_) => false,
        }
    }
    pub(crate) fn base_ty<'a>(self, ctxt: impl HasCompilerCtxt<'a, 'tcx>) -> ty::Ty<'tcx>
    where
        'tcx: 'a,
    {
        match self {
            MaybeRemoteRegionProjectionBase::Place(maybe_remote_place) => {
                let local_place: Place<'tcx> =
                    maybe_remote_place.related_local_place().local.into();
                local_place.ty(ctxt).ty
            }
            MaybeRemoteRegionProjectionBase::Const(c) => c.ty(),
        }
    }
    pub(crate) fn as_local_place_mut(&mut self) -> Option<&mut MaybeLabelledPlace<'tcx>> {
        match self {
            MaybeRemoteRegionProjectionBase::Place(p) => p.as_local_place_mut(),
            MaybeRemoteRegionProjectionBase::Const(_) => None,
        }
    }

    pub(crate) fn as_local_place(&self) -> Option<MaybeLabelledPlace<'tcx>> {
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

impl<'tcx, T: RegionProjectionBaseLike<'tcx>> PCGNodeLike<'tcx> for LifetimeProjection<'tcx, T> {
    fn to_pcg_node<C: Copy>(self, _ctxt: CompilerCtxt<'_, 'tcx, C>) -> PcgNode<'tcx> {
        self.with_base(self.base.to_maybe_remote_region_projection_base())
            .into()
    }
}

#[deprecated(note = "Use LifetimeProjectionLabel instead")]
pub type RegionProjectionLabel = LifetimeProjectionLabel;

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
pub enum LifetimeProjectionLabel {
    Location(SnapshotLocation),
    Future,
}

impl std::fmt::Display for LifetimeProjectionLabel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LifetimeProjectionLabel::Location(location) => write!(f, "{}", location),
            LifetimeProjectionLabel::Future => write!(f, "FUTURE"),
        }
    }
}

#[deprecated(note = "Use LifetimeProjection instead")]
pub type RegionProjection<'tcx, P = MaybeRemoteRegionProjectionBase<'tcx>> =
    LifetimeProjection<'tcx, P>;

/// A lifetime projection b↓r, where `b` is a base and `r` is a region.
#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy, Ord, PartialOrd)]
pub struct LifetimeProjection<'tcx, P = MaybeRemoteRegionProjectionBase<'tcx>> {
    pub(crate) base: P,
    pub(crate) region_idx: RegionIdx,
    label: Option<LifetimeProjectionLabel>,
    phantom: PhantomData<&'tcx ()>,
}

impl<'tcx> LabelPlaceWithContext<'tcx, LabelNodeContext> for LifetimeProjection<'tcx> {
    fn label_place_with_context(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        label_context: LabelNodeContext,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        if let Some(p) = self.base.as_local_place_mut() {
            p.label_place_with_context(predicate, labeller, label_context, ctxt)
        } else {
            false
        }
    }
}

impl<P> LifetimeProjection<'_, P> {
    pub(crate) fn is_future(&self) -> bool {
        self.label == Some(LifetimeProjectionLabel::Future)
    }
    pub(crate) fn label(&self) -> Option<LifetimeProjectionLabel> {
        self.label
    }
}

impl<'tcx> From<LifetimeProjection<'tcx, Place<'tcx>>> for LifetimeProjection<'tcx> {
    fn from(rp: LifetimeProjection<'tcx, Place<'tcx>>) -> Self {
        LifetimeProjection {
            base: rp.base.into(),
            region_idx: rp.region_idx,
            label: rp.label,
            phantom: PhantomData,
        }
    }
}

impl<'tcx, T, P> TryFrom<PcgNode<'tcx, T, P>> for LifetimeProjection<'tcx, P> {
    type Error = ();
    fn try_from(node: PcgNode<'tcx, T, P>) -> Result<Self, Self::Error> {
        match node {
            PcgNode::LifetimeProjection(rp) => Ok(rp),
            _ => Err(()),
        }
    }
}

impl<'tcx, P: Copy> LabelLifetimeProjection<'tcx> for LifetimeProjection<'tcx, P>
where
    MaybeRemoteRegionProjectionBase<'tcx>: From<P>,
{
    fn label_lifetime_projection(
        &mut self,
        predicate: &LabelLifetimeProjectionPredicate<'tcx>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> LabelLifetimeProjectionResult {
        if predicate.matches(self.rebase(), ctxt) {
            self.label = label;
            LabelLifetimeProjectionResult::Changed
        } else {
            LabelLifetimeProjectionResult::Unchanged
        }
    }
}

impl<'tcx> From<LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>>>
    for LifetimeProjection<'tcx, MaybeRemotePlace<'tcx>>
{
    fn from(value: LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>>) -> Self {
        LifetimeProjection {
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

impl<'tcx, T: RegionProjectionBaseLike<'tcx>> LifetimeProjection<'tcx, T> {
    pub(crate) fn is_invariant_in_type<'a>(&self, ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>) -> bool
    where
        'tcx: 'a,
    {
        let mut visitor = TyVarianceVisitor {
            ctxt: ctxt.bc_ctxt(),
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

impl<'tcx, T: RegionProjectionBaseLike<'tcx>> LifetimeProjection<'tcx, T> {
    #[must_use]
    pub(crate) fn with_placeholder_label<'a>(
        self,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> LifetimeProjection<'tcx, T>
    where
        'tcx: 'a,
    {
        self.with_label(Some(LifetimeProjectionLabel::Future), ctxt)
    }

    #[must_use]
    pub(crate) fn with_label<'a>(
        self,
        label: Option<LifetimeProjectionLabel>,
        _ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> LifetimeProjection<'tcx, T>
    where
        'tcx: 'a,
    {
        LifetimeProjection {
            base: self.base,
            region_idx: self.region_idx,
            label,
            phantom: PhantomData,
        }
    }
}
impl<'tcx> From<LifetimeProjection<'tcx, MaybeRemotePlace<'tcx>>> for LifetimeProjection<'tcx> {
    fn from(rp: LifetimeProjection<'tcx, MaybeRemotePlace<'tcx>>) -> Self {
        LifetimeProjection {
            base: rp.base.into(),
            region_idx: rp.region_idx,
            label: rp.label,
            phantom: PhantomData,
        }
    }
}

impl<'tcx> TryFrom<LifetimeProjection<'tcx>> for LifetimeProjection<'tcx, MaybeRemotePlace<'tcx>> {
    type Error = ();
    fn try_from(rp: LifetimeProjection<'tcx>) -> Result<Self, Self::Error> {
        match rp.base {
            MaybeRemoteRegionProjectionBase::Place(p) => Ok(LifetimeProjection {
                base: p,
                region_idx: rp.region_idx,
                label: rp.label,
                phantom: PhantomData,
            }),
            MaybeRemoteRegionProjectionBase::Const(_) => Err(()),
        }
    }
}

impl<'tcx> TryFrom<LifetimeProjection<'tcx>>
    for LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>>
{
    type Error = String;
    fn try_from(rp: LifetimeProjection<'tcx>) -> Result<Self, Self::Error> {
        match rp.base {
            MaybeRemoteRegionProjectionBase::Place(p) => Ok(LifetimeProjection {
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

impl<'tcx, P: RegionProjectionBaseLike<'tcx>> LifetimeProjection<'tcx, P> {
    pub fn base(&self) -> P {
        self.base
    }
}

impl<'tcx> LocalNodeLike<'tcx> for LifetimeProjection<'tcx, Place<'tcx>> {
    fn to_local_node<C: Copy>(self, _ctxt: CompilerCtxt<'_, 'tcx, C>) -> LocalNode<'tcx> {
        LocalNode::LifetimeProjection(self.with_base(MaybeLabelledPlace::Current(self.base)))
    }
}

impl<'tcx> LocalNodeLike<'tcx> for LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>> {
    fn to_local_node<C: Copy>(self, _repacker: CompilerCtxt<'_, 'tcx, C>) -> LocalNode<'tcx> {
        LocalNode::LifetimeProjection(self)
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

    fn region_projections<C: Copy>(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, C>,
    ) -> IndexVec<RegionIdx, LifetimeProjection<'tcx, Self>> {
        self.regions(ctxt)
            .into_iter()
            .map(|region| LifetimeProjection::new(region, *self, None, ctxt).unwrap())
            .collect()
    }
}

impl<
    'tcx,
    'a,
    T: RegionProjectionBaseLike<'tcx>
        + DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
> DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>
    for LifetimeProjection<'tcx, T>
{
    fn to_short_string(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    ) -> String {
        let label_part = match self.label {
            Some(LifetimeProjectionLabel::Location(location)) => format!(" {location}"),
            Some(LifetimeProjectionLabel::Future) => " FUTURE".to_string(),
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
    for LifetimeProjection<'tcx, T>
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

impl<T: std::fmt::Display> fmt::Display for LifetimeProjection<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}↓{:?}", self.base, self.region_idx)
    }
}

impl<'tcx> From<LifetimeProjection<'tcx, Place<'tcx>>>
    for LifetimeProjection<'tcx, MaybeRemotePlace<'tcx>>
{
    fn from(rp: LifetimeProjection<'tcx, Place<'tcx>>) -> Self {
        LifetimeProjection {
            base: rp.base.into(),
            region_idx: rp.region_idx,
            label: rp.label,
            phantom: PhantomData,
        }
    }
}

impl<'tcx> TryFrom<AbstractionGraphNode<'tcx>>
    for LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>>
{
    type Error = String;
    fn try_from(node: AbstractionGraphNode<'tcx>) -> Result<Self, Self::Error> {
        match *node {
            PcgNode::LifetimeProjection(rp) => rp.try_into(),
            PcgNode::Place(p) => Err(format!(
                "Place {:?} cannot be converted to a region projection",
                p
            )),
        }
    }
}

impl<'tcx> TryFrom<LifetimeProjection<'tcx, MaybeRemotePlace<'tcx>>>
    for LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>>
{
    type Error = String;
    fn try_from(rp: LifetimeProjection<'tcx, MaybeRemotePlace<'tcx>>) -> Result<Self, Self::Error> {
        Ok(LifetimeProjection {
            base: rp.base.try_into()?,
            region_idx: rp.region_idx,
            label: rp.label,
            phantom: PhantomData,
        })
    }
}

impl<'tcx> From<MaybeLabelledPlace<'tcx>> for MaybeRemoteRegionProjectionBase<'tcx> {
    fn from(place: MaybeLabelledPlace<'tcx>) -> Self {
        MaybeRemoteRegionProjectionBase::Place(place.into())
    }
}

impl<'tcx> From<LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>>> for LifetimeProjection<'tcx> {
    fn from(rp: LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>>) -> Self {
        LifetimeProjection {
            base: rp.base.into(),
            region_idx: rp.region_idx,
            label: rp.label,
            phantom: PhantomData,
        }
    }
}

impl<'tcx> From<LifetimeProjection<'tcx, Place<'tcx>>>
    for LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>>
{
    fn from(rp: LifetimeProjection<'tcx, Place<'tcx>>) -> Self {
        LifetimeProjection {
            base: rp.base.into(),
            region_idx: rp.region_idx,
            label: rp.label,
            phantom: PhantomData,
        }
    }
}

impl<'tcx, T: RegionProjectionBaseLike<'tcx> + HasPlace<'tcx>> HasPlace<'tcx>
    for LifetimeProjection<'tcx, T>
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
        LifetimeProjection::new(
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
                    LifetimeProjection::new(self.region(ctxt), base, self.label, ctxt)
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

    fn is_place(&self) -> bool {
        false
    }
}

impl<'tcx, T: RegionProjectionBaseLike<'tcx>> HasValidityCheck<'tcx>
    for LifetimeProjection<'tcx, T>
{
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

impl<'tcx, T: RegionProjectionBaseLike<'tcx>> LifetimeProjection<'tcx, T> {
    pub(crate) fn new<'a>(
        region: PcgRegion,
        base: T,
        label: Option<LifetimeProjectionLabel>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Result<Self, PcgInternalError>
    where
        'tcx: 'a,
    {
        let region_idx = base
            .regions(ctxt.ctxt())
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

    pub(crate) fn region<'a>(&self, ctxt: impl HasCompilerCtxt<'a, 'tcx>) -> PcgRegion
    where
        'tcx: 'a,
    {
        let regions = self.base.regions(ctxt.ctxt());
        if self.region_idx.index() >= regions.len() {
            unreachable!()
        } else {
            regions[self.region_idx]
        }
    }
}

impl<T: Copy> LifetimeProjection<'_, T> {
    pub fn place(&self) -> T {
        self.base
    }
}

impl<'tcx, T> LifetimeProjection<'tcx, T> {
    pub(crate) fn place_mut(&mut self) -> &mut T {
        &mut self.base
    }

    pub(crate) fn rebase<U: RegionProjectionBaseLike<'tcx> + From<T>>(
        self,
    ) -> LifetimeProjection<'tcx, U>
    where
        T: Copy,
    {
        self.with_base(self.base.into())
    }

    pub(crate) fn with_base<U: RegionProjectionBaseLike<'tcx>>(
        self,
        base: U,
    ) -> LifetimeProjection<'tcx, U> {
        LifetimeProjection {
            base,
            region_idx: self.region_idx,
            label: self.label,
            phantom: PhantomData,
        }
    }
}

impl<'tcx> LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>> {
    /// If the region projection is of the form `x↓'a` and `x` has type `&'a T` or `&'a mut T`,
    /// this returns `*x`.
    pub fn deref(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Option<MaybeLabelledPlace<'tcx>> {
        if self.base.ty_region(ctxt) == Some(self.region(ctxt)) {
            Some(self.base.project_deref(ctxt))
        } else {
            None
        }
    }
}

pub(crate) type LocalLifetimeProjection<'tcx> = LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>>;

impl<'tcx> LocalLifetimeProjection<'tcx> {
    pub fn to_region_projection(&self) -> LifetimeProjection<'tcx> {
        self.with_base(self.base.into())
    }
}

impl<'tcx> LabelPlaceWithContext<'tcx, LabelNodeContext> for LocalLifetimeProjection<'tcx> {
    fn label_place_with_context(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        label_context: LabelNodeContext,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.base
            .label_place_with_context(predicate, labeller, label_context, ctxt)
    }
}

impl<'tcx> LifetimeProjection<'tcx> {
    pub fn local(&self) -> Option<Local> {
        self.base.as_local_place().map(|p| p.local())
    }

    fn as_local_region_projection(
        &self,
    ) -> Option<LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>>> {
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
    pub fn deref(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Option<MaybeLabelledPlace<'tcx>> {
        self.as_local_region_projection()
            .and_then(|rp| rp.deref(ctxt))
    }
}

impl From<RemotePlace> for MaybeRemoteRegionProjectionBase<'_> {
    fn from(remote_place: RemotePlace) -> Self {
        MaybeRemoteRegionProjectionBase::Place(remote_place.into())
    }
}
