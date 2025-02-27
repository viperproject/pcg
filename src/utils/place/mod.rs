// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{
    cmp::Ordering,
    fmt::{Debug, Formatter, Result},
    hash::{Hash, Hasher},
    mem::discriminant,
};

use derive_more::{Deref, DerefMut};

use crate::rustc_interface::{
    ast::Mutability,
    data_structures::fx::FxHasher,
    index::IndexVec,
    middle::{
        mir::{Body, Local, Place as MirPlace, PlaceElem, PlaceRef, ProjectionElem},
        ty::{self, Ty, TyCtxt, TyKind},
    },
    target::abi::VariantIdx,
};

use super::{
    debug_info::DebugInfo, display::DisplayWithRepacker, validity::HasValidityCheck, PlaceRepacker,
};
use crate::utils::json::ToJsonWithRepacker;
use crate::{
    borrow_pcg::{
        borrow_pcg_edge::LocalNode,
        region_projection::{
            MaybeRemoteRegionProjectionBase, PCGRegion, RegionIdx, RegionProjection,
            RegionProjectionBaseLike,
        },
        visitor::extract_regions,
    },
    combined_pcs::{LocalNodeLike, PCGNode, PCGNodeLike},
};

pub mod corrected;
pub mod maybe_old;
pub mod maybe_remote;
pub mod remote;

#[derive(Clone, Copy, Deref, DerefMut)]
pub struct Place<'tcx>(
    #[deref]
    #[deref_mut]
    PlaceRef<'tcx>,
    DebugInfo<'static>,
);

impl<'tcx> From<Place<'tcx>> for PlaceRef<'tcx> {
    fn from(place: Place<'tcx>) -> Self {
        *place
    }
}

impl<'tcx> PartialOrd for Place<'tcx> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<'tcx> Ord for Place<'tcx> {
    fn cmp(&self, other: &Self) -> Ordering {
        if self == other {
            Ordering::Equal
        } else {
            let mut h1 = FxHasher::default();
            let mut h2 = FxHasher::default();
            self.hash(&mut h1);
            other.hash(&mut h2);
            match h1.finish().cmp(&h2.finish()) {
                Ordering::Equal => {
                    panic!("Places have same hash, but they aren't equal!")
                }
                other => other,
            }
        }
    }
}

impl<'tcx> ToJsonWithRepacker<'tcx> for Place<'tcx> {
    fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        serde_json::Value::String(self.to_short_string(repacker))
    }
}

impl<'tcx> LocalNodeLike<'tcx> for Place<'tcx> {
    fn to_local_node(self, _repacker: PlaceRepacker<'_, 'tcx>) -> LocalNode<'tcx> {
        LocalNode::Place(self.into())
    }
}

impl<'tcx> PCGNodeLike<'tcx> for Place<'tcx> {
    fn to_pcg_node(self, _repacker: PlaceRepacker<'_, 'tcx>) -> PCGNode<'tcx> {
        self.into()
    }
}

impl<'tcx> RegionProjectionBaseLike<'tcx> for Place<'tcx> {
    fn to_maybe_remote_region_projection_base(&self) -> MaybeRemoteRegionProjectionBase<'tcx> {
        (*self).into()
    }

    fn regions(&self, repacker: PlaceRepacker<'_, 'tcx>) -> IndexVec<RegionIdx, PCGRegion> {
        extract_regions(self.ty(repacker).ty)
    }
}

impl<'tcx> From<Place<'tcx>> for MaybeRemoteRegionProjectionBase<'tcx> {
    fn from(place: Place<'tcx>) -> Self {
        MaybeRemoteRegionProjectionBase::Place(place.into())
    }
}

impl<'tcx> HasValidityCheck<'tcx> for Place<'tcx> {
    fn check_validity(
        &self,
        _repacker: PlaceRepacker<'_, 'tcx>,
    ) -> std::result::Result<(), std::string::String> {
        Ok(())
    }
}

/// A trait for PCG nodes that contain a single place.
pub trait HasPlace<'tcx>: Sized {
    fn place(&self) -> Place<'tcx>;

    fn place_mut(&mut self) -> &mut Place<'tcx>;

    fn project_deeper(
        &self,
        elem: PlaceElem<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Option<Self>;

    fn iter_projections(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Vec<(Self, PlaceElem<'tcx>)>;
}

impl<'tcx> HasPlace<'tcx> for Place<'tcx> {
    fn place(&self) -> Place<'tcx> {
        *self
    }
    fn place_mut(&mut self) -> &mut Place<'tcx> {
        self
    }

    fn project_deeper(
        &self,
        elem: PlaceElem<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Option<Self> {
        Some(self.project_deeper(elem, repacker))
    }

    fn iter_projections(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> Vec<(Self, PlaceElem<'tcx>)> {
        self.0
            .iter_projections()
            .map(|(place, elem)| (place.into(), elem))
            .collect()
    }
}

impl<'tcx> Place<'tcx> {
    /// Projects the place deeper by one element.
    ///
    /// __IMPORTANT__: This method also attempts to "normalize" the type of the resulting
    /// place by inheriting from the type of the current place when possible. For example,
    /// in the following code:
    /// ```ignore
    /// struct F<'a>(&'a mut i32);
    /// let x: F<'x> = F(&mut 1);
    /// let y: 'y mut i32 = x.0
    /// ```
    /// we want the type of `x.0` to be 'x mut i32 and NOT 'y mut i32. However, in the
    /// MIR the `ProjectionElem::Field` for `.0` may have the type `'y mut i32`.
    ///
    /// To correct this, when projecting, we detect when the LHS is an ADT, and
    /// extract from the ADT type the expected type of the projection and
    /// replace the type.
    ///
    /// ```
    fn project_deeper(&self, elem: PlaceElem<'tcx>, repacker: PlaceRepacker<'_, 'tcx>) -> Self {
        let base_ty = self.ty(repacker);
        let corrected_elem = if let ProjectionElem::Field(field_idx, proj_ty) = elem {
            let expected_ty = match base_ty.ty.kind() {
                ty::TyKind::Adt(def, substs) => {
                    let variant = match base_ty.variant_index {
                        Some(v) => def.variant(v),
                        None => def.non_enum_variant(),
                    };
                    variant.fields[field_idx].ty(repacker.tcx(), substs)
                }
                ty::TyKind::Tuple(tys) => tys[field_idx.as_usize()],
                _ => proj_ty,
            };
            ProjectionElem::Field(field_idx, expected_ty)
        } else {
            elem
        };
        self.0
            .project_deeper(&[corrected_elem], repacker.tcx())
            .into()
    }

    pub(crate) fn compare_projections(
        self,
        other: Self,
    ) -> impl Iterator<Item = (bool, PlaceElem<'tcx>, PlaceElem<'tcx>)> {
        let left = self.projection.iter().copied();
        let right = other.projection.iter().copied();
        left.zip(right).map(|(e1, e2)| (elem_eq((e1, e2)), e1, e2))
    }
}

impl<'tcx> Place<'tcx> {
    pub fn new(local: Local, projection: &'tcx [PlaceElem<'tcx>]) -> Self {
        Self(PlaceRef { local, projection }, DebugInfo::new_static())
    }

    pub(crate) fn base_region_projection(
        self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Option<RegionProjection<'tcx, Self>> {
        match self.ty_region(repacker) {
            Some(region) => Some(RegionProjection::new(region, self.into(), repacker).unwrap()),
            None => None,
        }
    }

    pub fn projection(&self) -> &'tcx [PlaceElem<'tcx>] {
        self.0.projection
    }

    pub(crate) fn contains_unsafe_deref(&self, repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        for (p, proj) in self.iter_projections(repacker) {
            if p.ty(repacker).ty.is_unsafe_ptr() && matches!(proj, PlaceElem::Deref) {
                return true;
            }
        }
        false
    }

    pub(crate) fn ty_region(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Option<PCGRegion> {
        match self.ty(repacker).ty.kind() {
            TyKind::Ref(region, _, _) => Some((*region).into()),
            _ => None,
        }
    }

    pub fn prefix_place(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> Option<Place<'tcx>> {
        let (prefix, _) = self.last_projection()?;
        Some(Place::new(prefix.local, &prefix.projection))
    }

    /// In MIR, if a place is a field projection, then the type of the place
    /// will be the determined by the last projection. If the type of that place
    /// contains borrows, it appears that the associated regions are not necessarily
    /// the same as the one given by the parent struct. See [`Place::project_deeper`]
    /// for more information
    ///
    /// In the case that this place is a reference-typed field projection, this function
    /// returns a new place with the same data, but with the region of the reference determined
    /// by the parent struct. Otherwise, the place is returned unchanged.
    ///
    /// Note: This only considers the last projection, so the place isn't entirely "normalized"
    /// w.r.t the property the [`Place::project_deeper`] is intended to achieve
    pub fn with_inherent_region(self, repacker: PlaceRepacker<'_, 'tcx>) -> Self {
        if self.projection.is_empty() {
            return self;
        }
        let base_place = Place::new(self.local, &self.projection[..self.projection.len() - 1]);

        if let Some(elem) = self.projection.last() {
            base_place.project_deeper(*elem, repacker)
        } else {
            self
        }
    }

    pub fn region_projection(
        &self,
        idx: RegionIdx,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> RegionProjection<'tcx, Self> {
        self.region_projections(repacker)[idx]
    }

    #[tracing::instrument(skip(repacker))]
    pub(crate) fn regions(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> IndexVec<RegionIdx, PCGRegion> {
        extract_regions(self.ty(repacker).ty)
    }

    pub(crate) fn region_projections(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> IndexVec<RegionIdx, RegionProjection<'tcx, Self>> {
        let place = self.with_inherent_region(repacker);
        extract_regions(place.ty(repacker).ty)
            .iter()
            .map(|region| RegionProjection::new((*region).into(), place.into(), repacker).unwrap())
            .collect()
    }

    pub fn projection_index(
        &self,
        region: PCGRegion,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Option<RegionIdx> {
        extract_regions(self.ty(repacker).ty)
            .into_iter_enumerated()
            .find(|(_, r)| *r == region)
            .map(|(idx, _)| idx)
    }

    pub fn is_owned(&self, repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        !self
            .iter_projections(repacker)
            .into_iter()
            .any(|(place, elem)| elem == ProjectionElem::Deref && !place.ty(repacker).ty.is_box())
    }

    pub fn is_mut_ref(&self, body: &Body<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
        matches!(
            self.0.ty(body, tcx).ty.kind(),
            TyKind::Ref(_, _, Mutability::Mut)
        )
    }

    pub fn is_ref(&self, repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        self.0.ty(repacker.mir, repacker.tcx).ty.is_ref()
    }

    pub fn ref_mutability(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Option<Mutability> {
        self.0.ty(repacker.mir, repacker.tcx).ty.ref_mutability()
    }

    pub fn project_deref(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Self {
        assert!(
            self.ty(repacker).ty.is_ref() || self.ty(repacker).ty.is_box(),
            "Expected ref or box, got {:?}",
            self.ty(repacker).ty
        );
        Place::new(
            self.0.local,
            self.0
                .project_deeper(&[PlaceElem::Deref], repacker.tcx())
                .projection,
        )
    }

    /// Check if the place `left` is a prefix of `right` or vice versa. For example:
    ///
    /// +   `partial_cmp(x.f, y.f) == None`
    /// +   `partial_cmp(x.f, x.g) == None`
    /// +   `partial_cmp(x.f, x.f) == Some(Equal)`
    /// +   `partial_cmp(x.f.g, x.f) == Some(Suffix)`
    /// +   `partial_cmp(x.f, x.f.g) == Some(Prefix)`
    /// +   `partial_cmp(x as None, x as Some.0) == Some(Both)`
    ///
    /// The ultimate question this answers is: are the two places mutually
    /// exclusive (i.e. can we have both or not)?
    /// For example, all of the following are mutually exclusive:
    ///  - `x` and `x.f`
    ///  - `(x as Ok).0` and `(x as Err).0`
    ///  - `x[_1]` and `x[_2]`
    ///  - `x[2 of 11]` and `x[5 of 14]`
    /// But the following are not:
    ///  - `x` and `y`
    ///  - `x.f` and `x.g.h`
    ///  - `x[3 of 6]` and `x[4 of 6]`
    pub(crate) fn partial_cmp(self, right: Self) -> Option<PlaceOrdering> {
        if self.local != right.local {
            return None;
        }
        let diff = self.compare_projections(right).find(|(eq, _, _)| !eq);
        if let Some((_, left, right)) = diff {
            use ProjectionElem::*;
            fn is_index(elem: PlaceElem<'_>) -> bool {
                matches!(elem, Index(_) | ConstantIndex { .. } | Subslice { .. })
            }
            match (left, right) {
                (Field(..), Field(..)) => None,
                (
                    ConstantIndex {
                        min_length: l,
                        from_end: lfe,
                        ..
                    },
                    ConstantIndex {
                        min_length: r,
                        from_end: rfe,
                        ..
                    },
                ) if r == l && lfe == rfe => None,
                (Downcast(_, _), Downcast(_, _)) | (OpaqueCast(_), OpaqueCast(_)) => {
                    Some(PlaceOrdering::Both)
                }
                (left, right) if is_index(left) && is_index(right) => Some(PlaceOrdering::Both),
                diff => unreachable!("Unexpected diff: {diff:?}"),
            }
        } else {
            Some(self.projection.len().cmp(&right.projection.len()).into())
        }
    }

    /// Check if the place `self` is a prefix of `place`. For example:
    ///
    /// +   `is_prefix(x.f, x.f) == true`
    /// +   `is_prefix(x.f, x.f.g) == true`
    /// +   `is_prefix(x.f.g, x.f) == false`
    pub(crate) fn is_prefix(self, place: Self) -> bool {
        Self::partial_cmp(self, place)
            .map(|o| o == PlaceOrdering::Equal || o == PlaceOrdering::Prefix)
            .unwrap_or(false)
    }

    /// Check if the place `self` is a strict prefix of `place`, that is,
    /// `self` is a prefix of `place` and `self` != `place`.
    pub(crate) fn is_strict_prefix(self, place: Self) -> bool {
        self.is_prefix(place) && self != place
    }

    /// Check if the place `self` is an exact prefix of `place`. For example:
    ///
    /// +   `is_prefix(x.f, x.f) == false`
    /// +   `is_prefix(x.f, x.f.g) == true`
    /// +   `is_prefix(x.f, x.f.g.h) == false`
    pub fn is_prefix_exact(self, place: Self) -> bool {
        self.0.projection.len() + 1 == place.0.projection.len()
            && Self::partial_cmp(self, place)
                .map(|o| o == PlaceOrdering::Prefix)
                .unwrap_or(false)
    }

    /// Check if the place `self` is a prefix of `place` or vice versa. For example:
    ///
    /// +   `is_prefix(x.f, x.f) == None`
    /// +   `is_prefix(x.f, x.f.g) == Some(true)`
    /// +   `is_prefix(x.f.g, x.f) == Some(false)`
    /// +   `is_prefix(x.g, x.f) == None`
    pub(crate) fn either_prefix(self, place: Self) -> Option<bool> {
        Self::partial_cmp(self, place).and_then(|o| {
            if o == PlaceOrdering::Prefix {
                Some(true)
            } else if o == PlaceOrdering::Suffix {
                Some(false)
            } else {
                None
            }
        })
    }

    /// Returns `true` if either of the places can reach the other
    /// with a series of expand/collapse operations. Note that
    /// both operations are allowed and so e.g.
    /// related_to(`_1[_4]`, `_1[_3]`) == true
    pub fn related_to(self, right: Self) -> bool {
        self.partial_cmp(right).is_some()
    }

    pub fn common_prefix(self, other: Self) -> Self {
        assert_eq!(self.local, other.local);

        let max_len = std::cmp::min(self.projection.len(), other.projection.len());
        let common_prefix = self
            .compare_projections(other)
            .position(|(eq, _, _)| !eq)
            .unwrap_or(max_len);
        Self::new(self.local, &self.projection[..common_prefix])
    }

    pub fn joinable_to(self, to: Self) -> Self {
        assert!(self.is_prefix(to));
        let diff = to.projection.len() - self.projection.len();
        let to_proj = self.projection.len()
            + to.projection[self.projection.len()..]
                .iter()
                .position(|p| !matches!(p, ProjectionElem::Deref | ProjectionElem::Field(..)))
                .unwrap_or(diff);
        Self::new(self.local, &to.projection[..to_proj])
    }

    pub fn last_projection(self) -> Option<(Self, PlaceElem<'tcx>)> {
        self.0
            .last_projection()
            .map(|(place, proj)| (place.into(), proj))
    }

    pub fn last_projection_ty(self) -> Option<Ty<'tcx>> {
        self.last_projection().and_then(|(_, proj)| match proj {
            ProjectionElem::Field(_, ty) | ProjectionElem::OpaqueCast(ty) => Some(ty),
            _ => None,
        })
    }

    pub fn is_deref_of(self, other: Self) -> bool {
        self.projection.last() == Some(&ProjectionElem::Deref)
            && other.is_prefix(self)
            && other.projection.len() == self.projection.len() - 1
    }

    pub fn is_downcast_of(self, other: Self) -> Option<VariantIdx> {
        if let Some(ProjectionElem::Downcast(_, index)) = self.projection.last() {
            if other.is_prefix(self) && other.projection.len() == self.projection.len() - 1 {
                Some(*index)
            } else {
                None
            }
        } else {
            None
        }
    }

    pub fn is_deref(self) -> bool {
        self.projection.last() == Some(&ProjectionElem::Deref)
    }

    pub fn target_place(self) -> Option<Self> {
        if let Some(ProjectionElem::Deref) = self.projection.last() {
            Some(Place::new(
                self.local,
                &self.projection[..self.projection.len() - 1],
            ))
        } else {
            None
        }
    }

    pub fn nearest_owned_place(self, repacker: PlaceRepacker<'_, 'tcx>) -> Self {
        if self.is_owned(repacker) {
            return self;
        }
        for (place, _) in self.iter_projections(repacker).into_iter().rev() {
            if place.is_owned(repacker) {
                return place;
            }
        }
        unreachable!()
    }

    pub fn debug_info(&self) -> DebugInfo<'static> {
        self.1
    }
}

impl<'tcx> Debug for Place<'tcx> {
    fn fmt(&self, fmt: &mut Formatter) -> Result {
        for elem in self.projection.iter().rev() {
            match elem {
                ProjectionElem::OpaqueCast(_) | ProjectionElem::Downcast(_, _) => {
                    write!(fmt, "(").unwrap();
                }
                ProjectionElem::Deref => {
                    write!(fmt, "(*").unwrap();
                }
                ProjectionElem::Field(_, _)
                | ProjectionElem::Index(_)
                | ProjectionElem::ConstantIndex { .. }
                | ProjectionElem::Subslice { .. } => {}
                ProjectionElem::Subtype(_) => todo!(),
            }
        }

        write!(fmt, "{:?}", self.local)?;

        for &elem in self.projection.iter() {
            match elem {
                ProjectionElem::OpaqueCast(ty) => {
                    write!(fmt, "@{ty})")?;
                }
                ProjectionElem::Downcast(Some(name), _index) => {
                    write!(fmt, "@{name})")?;
                }
                ProjectionElem::Downcast(None, index) => {
                    write!(fmt, "@variant#{index:?})")?;
                }
                ProjectionElem::Deref => {
                    write!(fmt, ")")?;
                }
                ProjectionElem::Field(field, _ty) => {
                    write!(fmt, ".{:?}", field.index())?;
                }
                ProjectionElem::Index(ref index) => {
                    write!(fmt, "[{index:?}]")?;
                }
                ProjectionElem::ConstantIndex {
                    offset,
                    min_length,
                    from_end: false,
                } => {
                    write!(fmt, "[{offset:?} of {min_length:?}]")?;
                }
                ProjectionElem::ConstantIndex {
                    offset,
                    min_length,
                    from_end: true,
                } => {
                    write!(fmt, "[-{offset:?} of {min_length:?}]")?;
                }
                ProjectionElem::Subslice {
                    from,
                    to: 0,
                    from_end: true,
                } => {
                    write!(fmt, "[{from:?}:]")?;
                }
                ProjectionElem::Subslice {
                    from: 0,
                    to,
                    from_end: true,
                } => {
                    write!(fmt, "[:-{to:?}]")?;
                }
                ProjectionElem::Subslice {
                    from,
                    to,
                    from_end: true,
                } => {
                    write!(fmt, "[{from:?}:-{to:?}]")?;
                }
                ProjectionElem::Subslice {
                    from,
                    to,
                    from_end: false,
                } => {
                    write!(fmt, "[{from:?}..{to:?}]")?;
                }
                ProjectionElem::Subtype(_) => todo!(),
            }
        }

        Ok(())
    }
}

fn elem_eq<'tcx>(to_cmp: (PlaceElem<'tcx>, PlaceElem<'tcx>)) -> bool {
    use ProjectionElem::*;
    match to_cmp {
        (Field(left, _), Field(right, _)) => left == right,
        (Downcast(_, left), Downcast(_, right)) => left == right,
        (left, right) => left == right,
    }
}

impl<'tcx> PartialEq for Place<'tcx> {
    fn eq(&self, other: &Self) -> bool {
        self.local == other.local
            && self.projection.len() == other.projection.len()
            && self.compare_projections(*other).all(|(eq, _, _)| eq)
    }
}
impl Eq for Place<'_> {}

impl Hash for Place<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.local.hash(state);
        let projection = self.0.projection;
        for &pe in projection {
            match pe {
                ProjectionElem::Field(field, _) => {
                    discriminant(&pe).hash(state);
                    field.hash(state);
                }
                ProjectionElem::Downcast(_, variant) => {
                    discriminant(&pe).hash(state);
                    variant.hash(state);
                }
                _ => pe.hash(state),
            }
        }
    }
}

impl<'tcx> From<PlaceRef<'tcx>> for Place<'tcx> {
    fn from(value: PlaceRef<'tcx>) -> Self {
        Self(value, DebugInfo::new_static())
    }
}
impl<'tcx> From<MirPlace<'tcx>> for Place<'tcx> {
    fn from(value: MirPlace<'tcx>) -> Self {
        Self(value.as_ref(), DebugInfo::new_static())
    }
}
impl<'tcx> From<Local> for Place<'tcx> {
    fn from(value: Local) -> Self {
        MirPlace::from(value).into()
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum PlaceOrdering {
    // For example `x.f` to `x.f.g`.
    Prefix,
    // For example `x.f` and `x.f`.
    Equal,
    // For example `x.f.g` to `x.f`.
    Suffix,
    // Both places share a common prefix, but are not related by prefix or suffix.
    // For example `x.f` and `x.h`
    Both,
}

impl PlaceOrdering {
    pub fn is_eq(self) -> bool {
        matches!(self, PlaceOrdering::Equal)
    }
    pub fn is_prefix(self) -> bool {
        matches!(self, PlaceOrdering::Prefix)
    }
    pub fn is_suffix(self) -> bool {
        matches!(self, PlaceOrdering::Suffix)
    }
    pub fn is_both(self) -> bool {
        matches!(self, PlaceOrdering::Both)
    }
}

impl From<Ordering> for PlaceOrdering {
    fn from(ordering: Ordering) -> Self {
        match ordering {
            Ordering::Less => PlaceOrdering::Prefix,
            Ordering::Equal => PlaceOrdering::Equal,
            Ordering::Greater => PlaceOrdering::Suffix,
        }
    }
}
impl From<PlaceOrdering> for Option<Ordering> {
    fn from(ordering: PlaceOrdering) -> Self {
        match ordering {
            PlaceOrdering::Prefix => Some(Ordering::Less),
            PlaceOrdering::Equal => Some(Ordering::Equal),
            PlaceOrdering::Suffix => Some(Ordering::Greater),
            PlaceOrdering::Both => None,
        }
    }
}
