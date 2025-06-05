use std::hash::Hash;
use std::{fmt, marker::PhantomData};

use derive_more::{Display, From, TryFrom};
use serde_json::json;

use super::has_pcs_elem::{HasPcgElems, LabelRegionProjection};
use super::{
    abstraction_graph_constructor::AbstractionGraphNode, borrow_pcg_edge::LocalNode,
    visitor::extract_regions,
};
use crate::borrow_pcg::edge_data::LabelPlacePredicate;
use crate::borrow_pcg::has_pcs_elem::LabelPlace;
use crate::borrow_pcg::latest::Latest;
use crate::pcg::{PCGInternalError, PcgError};
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
            mir::{self, Const, Local, PlaceElem},
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

impl<'tcx> DisplayWithCompilerCtxt<'tcx> for RegionVid {
    fn to_short_string(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> String {
        if let Some(string) = ctxt.bc.override_region_debug_string(*self) {
            string.to_string()
        } else {
            format!("{self:?}")
        }
        // let origin = ctxt.bc.region_inference_ctxt().definitions[*self].origin;
        // match origin {
        //     RegionVariableOrigin::BoundRegion(span, BoundRegionKind::Named(_, symbol), _) => {
        //         let span_str = if let Some(source_map) = get_source_map() {
        //             source_map.span_to_string(span, FileNameDisplayPreference::Short)
        //         } else {
        //             format!("{:?}", span)
        //         };
        //         format!("{} at {}: {:?}", symbol, span_str, self)
        //     }
        //     RegionVariableOrigin::RegionParameterDefinition(_span, symbol) => symbol.to_string(),

        //     // `MiscVariable` is used as a placeholder for uncategorized, so we just
        //     // display it as normal
        //     RegionVariableOrigin::MiscVariable(_) => {
        //         format!("{:?}", self)
        //     }

        //     // Most NLL region variables have this origin, so just display it as normal
        //     RegionVariableOrigin::Nll(NllRegionVariableOrigin::Existential {
        //         from_forall: false,
        //     }) => {
        //         format!("{:?}", self)
        //     }
        //     other => {
        //         format!("{:?}: {:?}", other, self)
        //     }
        // }
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

impl<'tcx> DisplayWithCompilerCtxt<'tcx> for PcgRegion {
    fn to_short_string(&self, repacker: CompilerCtxt<'_, 'tcx>) -> String {
        self.to_string(Some(repacker))
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

/// The index of a region within a type. We store the index instead of the
/// region itself to appropriately maintain the same relative region for
/// handling moves.
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

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy, Display, From, TryFrom)]
pub enum MaybeRemoteRegionProjectionBase<'tcx> {
    Place(MaybeRemotePlace<'tcx>),
    Const(Const<'tcx>),
}

impl<'tcx> MaybeRemoteRegionProjectionBase<'tcx> {
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
}
impl<'tcx> HasValidityCheck<'tcx> for MaybeRemoteRegionProjectionBase<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        match self {
            MaybeRemoteRegionProjectionBase::Place(p) => p.check_validity(ctxt),
            MaybeRemoteRegionProjectionBase::Const(_) => todo!(),
        }
    }
}

impl<'tcx> ToJsonWithCompilerCtxt<'tcx> for MaybeRemoteRegionProjectionBase<'tcx> {
    fn to_json(&self, repacker: CompilerCtxt<'_, 'tcx>) -> serde_json::Value {
        match self {
            MaybeRemoteRegionProjectionBase::Place(p) => p.to_json(repacker),
            MaybeRemoteRegionProjectionBase::Const(_) => todo!(),
        }
    }
}

impl<'tcx> DisplayWithCompilerCtxt<'tcx> for MaybeRemoteRegionProjectionBase<'tcx> {
    fn to_short_string(&self, repacker: CompilerCtxt<'_, 'tcx>) -> String {
        match self {
            MaybeRemoteRegionProjectionBase::Place(p) => p.to_short_string(repacker),
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

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy, Ord, PartialOrd, From)]
pub(crate) enum RegionProjectionLabel {
    Location(SnapshotLocation),
    Placeholder,
}

impl From<mir::Location> for RegionProjectionLabel {
    fn from(location: mir::Location) -> Self {
        RegionProjectionLabel::Location(location.into())
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy, Ord, PartialOrd)]
pub struct RegionProjection<'tcx, P = MaybeRemoteRegionProjectionBase<'tcx>> {
    pub(crate) base: P,
    pub(crate) region_idx: RegionIdx,
    pub(crate) label: Option<RegionProjectionLabel>,
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

impl<'tcx, P> RegionProjection<'tcx, P> {
    pub(crate) fn is_placeholder(&self) -> bool {
        self.label == Some(RegionProjectionLabel::Placeholder)
    }
}

impl<'tcx> LocalRegionProjection<'tcx> {
    pub(crate) fn is_mutable(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        let place = self.base.place();
        place.iter_places(ctxt).iter().all(|p| {
            p.ty(ctxt)
                .ty
                .ref_mutability()
                .is_none_or(|mutability| mutability.is_mut())
        })
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
        projection: &RegionProjection<'tcx, MaybeOldPlace<'tcx>>,
        label: Option<RegionProjectionLabel>,
        _repacker: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        if self.region_idx == projection.region_idx
            && self.base == projection.base.into()
            && self.label == projection.label
        {
            self.label = label;
            true
        } else {
            false
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

/// Determines if a region `'r` is nested under a mutable reference for a type
/// `t`, such that a function taking a value `v` of type `t` can mutate the (set
/// of) references of lifetime `'r` in `v`.
struct MutableNestedReferenceChecker<'mir, 'tcx, C: Copy> {
    ctxt: CompilerCtxt<'mir, 'tcx, C>,
    target: PcgRegion,
    found: bool,
}

impl<'mir, 'tcx, C: Copy> MutableNestedReferenceChecker<'mir, 'tcx, C> {
    fn new(ctxt: CompilerCtxt<'mir, 'tcx, C>, target: PcgRegion) -> Self {
        Self {
            ctxt,
            target,
            found: false,
        }
    }
}

impl<'tcx, C: Copy> TypeVisitor<ty::TyCtxt<'tcx>> for MutableNestedReferenceChecker<'_, 'tcx, C> {
    fn visit_ty(&mut self, t: ty::Ty<'tcx>) {
        if self.found {
            return;
        }

        match t.kind() {
            TyKind::RawPtr(ty, mutbl) | TyKind::Ref(_, ty, mutbl) => {
                if mutbl.is_mut() {
                    if extract_regions(*ty, self.ctxt)
                        .iter()
                        .any(|r| self.target == *r)
                    {
                        self.found = true;
                    }
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

impl<'tcx, T: RegionProjectionBaseLike<'tcx> + HasPlace<'tcx>> RegionProjection<'tcx, T> {
    // Returns true iff the region is nested under a mutable reference, w.r.t
    // the local of the place of this region projection
    pub(crate) fn is_nested_under_mut_ref<C: Copy>(self, ctxt: CompilerCtxt<'_, 'tcx, C>) -> bool {
        let mut checker = MutableNestedReferenceChecker::new(ctxt, self.region(ctxt));
        let local_place: Place<'tcx> = self.base.place().local.into();
        local_place.ty(ctxt).visit_with(&mut checker);
        checker.found
    }
}

impl<'tcx, T: RegionProjectionBaseLike<'tcx>> RegionProjection<'tcx, T> {
    pub(crate) fn label_projection(
        self,
        label: RegionProjectionLabel,
    ) -> RegionProjection<'tcx, T> {
        RegionProjection {
            base: self.base,
            region_idx: self.region_idx,
            label: Some(label),
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
    type Error = ();
    fn try_from(rp: RegionProjection<'tcx>) -> Result<Self, Self::Error> {
        match rp.base {
            MaybeRemoteRegionProjectionBase::Place(p) => Ok(RegionProjection {
                base: p.try_into()?,
                region_idx: rp.region_idx,
                label: rp.label,
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
    fn to_local_node<C: Copy>(self, _ctxt: CompilerCtxt<'_, 'tcx, C>) -> LocalNode<'tcx> {
        LocalNode::RegionProjection(self.with_base(MaybeOldPlace::Current { place: self.base }))
    }
}

impl<'tcx> LocalNodeLike<'tcx> for RegionProjection<'tcx, MaybeOldPlace<'tcx>> {
    fn to_local_node<C: Copy>(self, _repacker: CompilerCtxt<'_, 'tcx, C>) -> LocalNode<'tcx> {
        LocalNode::RegionProjection(self)
    }
}

pub trait RegionProjectionBaseLike<'tcx>:
    Copy
    + std::fmt::Debug
    + std::hash::Hash
    + Eq
    + PartialEq
    + ToJsonWithCompilerCtxt<'tcx>
    + DisplayWithCompilerCtxt<'tcx>
{
    fn regions<C: Copy>(
        &self,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> IndexVec<RegionIdx, PcgRegion>;

    fn to_maybe_remote_region_projection_base(&self) -> MaybeRemoteRegionProjectionBase<'tcx>;
}

impl<'tcx, T: RegionProjectionBaseLike<'tcx>> DisplayWithCompilerCtxt<'tcx>
    for RegionProjection<'tcx, T>
{
    fn to_short_string(&self, repacker: CompilerCtxt<'_, 'tcx>) -> String {
        let label_part = match self.label {
            Some(RegionProjectionLabel::Location(location)) => format!(" {location}"),
            Some(RegionProjectionLabel::Placeholder) => " FUTURE".to_string(),
            _ => "".to_string(),
        };
        format!(
            "{}↓{}{}",
            self.base.to_short_string(repacker),
            self.region(repacker).to_short_string(repacker),
            label_part
        )
    }
}

impl<'tcx, T: RegionProjectionBaseLike<'tcx>> ToJsonWithCompilerCtxt<'tcx>
    for RegionProjection<'tcx, T>
{
    fn to_json(&self, repacker: CompilerCtxt<'_, 'tcx>) -> serde_json::Value {
        json!({
            "place": self.base.to_json(repacker),
            "region": self.region(repacker).to_string(Some(repacker)),
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
    type Error = ();
    fn try_from(node: AbstractionGraphNode<'tcx>) -> Result<Self, Self::Error> {
        match *node {
            PCGNode::RegionProjection(rp) => rp.try_into(),
            PCGNode::Place(_) => Err(()),
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
        repacker: CompilerCtxt<'_, 'tcx, C>,
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

    pub(crate) fn region<C: Copy>(&self, repacker: CompilerCtxt<'_, 'tcx, C>) -> PcgRegion {
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
    ) -> RegionProjection<'tcx, U> {
        let result = RegionProjection {
            base,
            region_idx: self.region_idx,
            label: self.label,
            phantom: PhantomData,
        };
        result
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
}

impl<'tcx> RegionProjection<'tcx> {
    pub fn local(&self) -> Option<Local> {
        self.base.as_local_place().map(|p| p.local())
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
