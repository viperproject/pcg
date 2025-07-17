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

use crate::{
    borrow_pcg::borrow_pcg_expansion::PlaceExpansion,
    free_pcs::RepackGuide,
    pcg::{PcgError, PcgUnsupportedError},
    rustc_interface::{
        ast::Mutability,
        data_structures::fx::FxHasher,
        index::IndexVec,
        middle::{
            mir::{Local, Place as MirPlace, PlaceElem, PlaceRef, ProjectionElem},
            ty::{self, Ty, TyKind},
        },
        VariantIdx,
    },
    utils::data_structures::HashSet,
};

#[cfg(feature = "debug_info")]
use super::debug_info::DebugInfo;

use super::{display::DisplayWithCompilerCtxt, validity::HasValidityCheck, CompilerCtxt};
use crate::utils::json::ToJsonWithCompilerCtxt;
use crate::{
    borrow_pcg::{
        borrow_pcg_edge::LocalNode,
        region_projection::{
            MaybeRemoteRegionProjectionBase, PcgRegion, RegionIdx, RegionProjection,
            RegionProjectionBaseLike,
        },
        visitor::extract_regions,
    },
    pcg::{LocalNodeLike, PCGNode, PCGNodeLike},
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
    #[cfg(feature = "debug_info")] DebugInfo<'static>,
);

impl<'tcx> From<Place<'tcx>> for PlaceRef<'tcx> {
    fn from(place: Place<'tcx>) -> Self {
        *place
    }
}

impl PartialOrd for Place<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Place<'_> {
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

impl<'tcx, BC: Copy> ToJsonWithCompilerCtxt<'tcx, BC> for Place<'tcx> {
    fn to_json(&self, repacker: CompilerCtxt<'_, 'tcx, BC>) -> serde_json::Value {
        serde_json::Value::String(self.to_short_string(repacker))
    }
}

impl<'tcx> LocalNodeLike<'tcx> for Place<'tcx> {
    fn to_local_node<C: Copy>(self, _repacker: CompilerCtxt<'_, 'tcx, C>) -> LocalNode<'tcx> {
        LocalNode::Place(self.into())
    }
}

impl<'tcx> PCGNodeLike<'tcx> for Place<'tcx> {
    fn to_pcg_node<C: Copy>(self, _repacker: CompilerCtxt<'_, 'tcx, C>) -> PCGNode<'tcx> {
        self.into()
    }
}

impl<'tcx> RegionProjectionBaseLike<'tcx> for Place<'tcx> {
    fn to_maybe_remote_region_projection_base(&self) -> MaybeRemoteRegionProjectionBase<'tcx> {
        (*self).into()
    }

    fn regions<C: Copy>(
        &self,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> IndexVec<RegionIdx, PcgRegion> {
        extract_regions(self.ty(repacker).ty, repacker)
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
        _ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> std::result::Result<(), std::string::String> {
        Ok(())
    }
}

/// A trait for PCG nodes that contain a single place.
pub trait HasPlace<'tcx>: Sized {
    fn place(&self) -> Place<'tcx>;

    fn place_mut(&mut self) -> &mut Place<'tcx>;

    fn project_deeper<C: Copy>(
        &self,
        elem: PlaceElem<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> std::result::Result<Self, PcgError>;

    fn iter_projections<C: Copy>(
        &self,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> Vec<(Self, PlaceElem<'tcx>)>;
}

impl<'tcx> HasPlace<'tcx> for Place<'tcx> {
    fn place(&self) -> Place<'tcx> {
        *self
    }
    fn place_mut(&mut self) -> &mut Place<'tcx> {
        self
    }

    fn project_deeper<C: Copy>(
        &self,
        elem: PlaceElem<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> std::result::Result<Self, PcgError> {
        Place::project_deeper(*self, elem, repacker).map_err(PcgError::unsupported)
    }

    fn iter_projections<C: Copy>(
        &self,
        _repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> Vec<(Self, PlaceElem<'tcx>)> {
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
    /// Returns an error if the projection would be illegal
    ///
    /// ```
    pub(crate) fn project_deeper<C: Copy>(
        self,
        elem: PlaceElem<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> std::result::Result<Self, PcgUnsupportedError> {
        let base_ty = self.ty(repacker);
        if matches!(
            elem,
            ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. }
        ) && base_ty.ty.builtin_index().is_none()
        {
            return Err(PcgUnsupportedError::IndexingNonIndexableType);
        }
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
        Ok(self
            .0
            .project_deeper(&[corrected_elem], repacker.tcx())
            .into())
    }

    #[rustversion::since(2025-05-24)]
    pub(crate) fn is_raw_ptr(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        self.ty(ctxt).ty.is_raw_ptr()
    }

    #[rustversion::before(2025-05-24)]
    pub(crate) fn is_raw_ptr(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        self.ty(ctxt).ty.is_unsafe_ptr()
    }

    pub(crate) fn compare_projections(
        self,
        other: Self,
    ) -> impl Iterator<Item = (bool, PlaceElem<'tcx>, PlaceElem<'tcx>)> {
        let left = self.projection.iter().copied();
        let right = other.projection.iter().copied();
        left.zip(right).map(|(e1, e2)| (elem_eq((e1, e2)), e1, e2))
    }

    pub(crate) fn iter_places<C: Copy>(self, repacker: CompilerCtxt<'_, 'tcx, C>) -> Vec<Self> {
        let mut places = self
            .iter_projections(repacker)
            .into_iter()
            .map(|(place, _)| place)
            .collect::<Vec<_>>();
        places.push(self);
        places
    }

    pub(crate) fn parent_place(self) -> Option<Self> {
        let (prefix, _) = self.last_projection()?;
        Some(Place::new(prefix.local, prefix.projection))
    }
}

impl<'tcx> Place<'tcx> {
    #[cfg(feature = "debug_info")]
    pub fn new(local: Local, projection: &'tcx [PlaceElem<'tcx>]) -> Self {
        Self(PlaceRef { local, projection }, DebugInfo::new_static())
    }

    #[cfg(not(feature = "debug_info"))]
    pub fn new(local: Local, projection: &'tcx [PlaceElem<'tcx>]) -> Self {
        Self(PlaceRef { local, projection })
    }

    pub(crate) fn expansion(
        self,
        guide: Option<RepackGuide>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> PlaceExpansion<'tcx> {
        if let Some(guide) = guide {
            guide.into()
        } else if self.ty(ctxt).ty.is_box() {
            PlaceExpansion::Deref
        } else {
            match self.ty(ctxt).ty.kind() {
                ty::TyKind::Adt(adt_def, substs) => {
                    let variant = match self.ty(ctxt).variant_index {
                        Some(v) => adt_def.variant(v),
                        None => adt_def.non_enum_variant(),
                    };
                    PlaceExpansion::Fields(
                        variant
                            .fields
                            .iter()
                            .enumerate()
                            .map(|(i, field)| (i.into(), field.ty(ctxt.tcx(), substs)))
                            .collect(),
                    )
                }
                ty::TyKind::Tuple(tys) => PlaceExpansion::Fields(
                    tys.iter()
                        .enumerate()
                        .map(|(i, ty)| (i.into(), ty))
                        .collect(),
                ),
                _ => unreachable!("Unexpected type: {:?}", self.ty(ctxt).ty),
            }
        }
    }

    pub(crate) fn expansion_places(
        self,
        expansion: &PlaceExpansion<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> Vec<Place<'tcx>> {
        let mut places = Vec::new();
        for elem in expansion.elems() {
            places.push(self.project_deeper(elem, repacker).unwrap());
        }
        places
    }

    pub(crate) fn base_region_projection<C: Copy>(
        self,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> Option<RegionProjection<'tcx, Self>> {
        self.ty_region(repacker)
            .map(|region| RegionProjection::new(region, self, None, repacker).unwrap())
    }

    pub fn projection(&self) -> &'tcx [PlaceElem<'tcx>] {
        self.0.projection
    }

    pub(crate) fn contains_unsafe_deref(&self, repacker: CompilerCtxt<'_, 'tcx>) -> bool {
        for (p, proj) in self.iter_projections(repacker) {
            if p.is_raw_ptr(repacker) && matches!(proj, PlaceElem::Deref) {
                return true;
            }
        }
        false
    }

    pub(crate) fn has_lifetimes_under_unsafe_ptr(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        fn ty_has_lifetimes_under_unsafe_ptr<'tcx>(
            ty: Ty<'tcx>,
            seen: &mut HashSet<Ty<'tcx>>,
            ctxt: CompilerCtxt<'_, 'tcx>,
        ) -> bool {
            if seen.contains(&ty) {
                return false;
            }
            seen.insert(ty);
            if extract_regions(ty, ctxt).is_empty() {
                return false;
            }
            if ty.is_unsafe_ptr() {
                return true;
            }
            let field_tys: Vec<Ty<'tcx>> = match ty.kind() {
                TyKind::Array(ty, _) => vec![*ty],
                TyKind::Slice(ty) => vec![*ty],
                TyKind::Adt(def, substs) => {
                    if ty.is_box() {
                        vec![substs.get(0).unwrap().expect_ty()]
                    } else {
                        def.all_fields()
                            .map(|f| f.ty(ctxt.tcx, substs))
                            .collect::<Vec<_>>()
                    }
                }
                TyKind::Tuple(slice) => slice.iter().collect::<Vec<_>>(),
                TyKind::Closure(_, substs) => {
                    substs.as_closure().upvar_tys().iter().collect::<Vec<_>>()
                }
                TyKind::Ref(_, ty, _) => vec![*ty],
                TyKind::Bool => todo!(),
                TyKind::Char => todo!(),
                TyKind::Int(int_ty) => todo!(),
                TyKind::Uint(uint_ty) => todo!(),
                TyKind::Float(float_ty) => todo!(),
                TyKind::Adt(_, _) => todo!(),
                TyKind::Foreign(_) => todo!(),
                TyKind::Str => todo!(),
                TyKind::Array(_, _) => todo!(),
                TyKind::Pat(_, _) => todo!(),
                TyKind::Slice(_) => todo!(),
                TyKind::RawPtr(_, mutability) => todo!(),
                TyKind::Ref(_, _, mutability) => todo!(),
                TyKind::FnDef(_, _) => todo!(),
                TyKind::FnPtr(binder, fn_header) => todo!(),
                TyKind::Dynamic(_, _, dyn_kind) => vec![],
                TyKind::Closure(_, _) => todo!(),
                TyKind::CoroutineClosure(_, _) => todo!(),
                TyKind::Coroutine(_, _) => todo!(),
                TyKind::CoroutineWitness(_, _) => todo!(),
                TyKind::Never => todo!(),
                TyKind::Tuple(_) => todo!(),
                TyKind::Alias(_, _) => vec![],
                TyKind::Param(_) => todo!(),
                TyKind::Bound(debruijn_index, _) => todo!(),
                TyKind::Placeholder(_) => todo!(),
                TyKind::Infer(infer_ty) => todo!(),
                TyKind::Error(_) => todo!(),
            };
            field_tys
                .iter()
                .any(|ty| ty_has_lifetimes_under_unsafe_ptr(*ty, seen, ctxt))
        }
        ty_has_lifetimes_under_unsafe_ptr(self.ty(ctxt).ty, &mut HashSet::default(), ctxt)
    }

    pub(crate) fn ty_region<C: Copy>(&self, ctxt: CompilerCtxt<'_, 'tcx, C>) -> Option<PcgRegion> {
        match self.ty(ctxt).ty.kind() {
            TyKind::Ref(region, _, _) => Some((*region).into()),
            _ => None,
        }
    }

    pub fn prefix_place(&self) -> Option<Place<'tcx>> {
        let (prefix, _) = self.last_projection()?;
        Some(Place::new(prefix.local, prefix.projection))
    }

    /// The type of a MIR place is not necessarily determined by the syntactic projection
    /// elems from the root place: the projection elements may contain additional type information
    /// depending on how the place is used. Therefore, the same (syntactic) place may in fact
    /// be different due to the different types in its projection.
    ///
    /// This function converts the Place into a canonical form by re-projecting the place
    /// from its local, and using types derived from the root place as the types associated
    /// with Field region projections.
    pub fn with_inherent_region<C: Copy>(self, repacker: CompilerCtxt<'_, 'tcx, C>) -> Self {
        let mut proj_iter = self.iter_projections(repacker).into_iter();
        let mut place = if let Some((place, elem)) = proj_iter.next() {
            place.project_deeper(elem, repacker).unwrap()
        } else {
            return self;
        };
        for (_, elem) in proj_iter {
            if let Ok(next_place) = place.project_deeper(elem, repacker) {
                place = next_place;
            } else {
                // We cannot normalize the place (probably due to indexing of an
                // alias type that we cannot resolve). For now we just return the
                // original place.
                return self;
            }
        }
        place
    }

    pub fn region_projection(
        &self,
        idx: RegionIdx,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> RegionProjection<'tcx, Self> {
        self.region_projections(repacker)[idx]
    }

    pub fn regions<C: Copy>(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, C>,
    ) -> IndexVec<RegionIdx, PcgRegion> {
        extract_regions(self.ty(ctxt).ty, ctxt)
    }

    pub(crate) fn has_region_projections(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        !self.regions(ctxt).is_empty()
    }

    pub(crate) fn region_projections<C: Copy>(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, C>,
    ) -> IndexVec<RegionIdx, RegionProjection<'tcx, Self>> {
        let place = self.with_inherent_region(ctxt);
        extract_regions(place.ty(ctxt).ty, ctxt)
            .iter()
            .map(|region| RegionProjection::new(*region, place, None, ctxt).unwrap())
            .collect()
    }

    pub fn projection_index(
        &self,
        region: PcgRegion,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> Option<RegionIdx> {
        extract_regions(self.ty(repacker).ty, repacker)
            .into_iter_enumerated()
            .find(|(_, r)| *r == region)
            .map(|(idx, _)| idx)
    }

    pub fn is_owned<C: Copy>(&self, repacker: CompilerCtxt<'_, 'tcx, C>) -> bool {
        !self
            .iter_projections(repacker)
            .into_iter()
            .any(|(place, elem)| elem == ProjectionElem::Deref && !place.ty(repacker).ty.is_box())
    }

    pub fn is_mut_ref(&self, repacker: CompilerCtxt<'_, 'tcx>) -> bool {
        matches!(
            self.0.ty(repacker.mir, repacker.tcx).ty.kind(),
            TyKind::Ref(_, _, Mutability::Mut)
        )
    }

    pub(crate) fn is_shared_ref(self, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        matches!(self.ref_mutability(ctxt), Some(Mutability::Not))
    }

    pub fn is_ref<C: Copy>(&self, ctxt: CompilerCtxt<'_, 'tcx, C>) -> bool {
        self.0.ty(ctxt.mir, ctxt.tcx).ty.is_ref()
    }

    pub fn ref_mutability<C: Copy>(
        &self,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> Option<Mutability> {
        self.0.ty(repacker.mir, repacker.tcx).ty.ref_mutability()
    }

    pub fn project_deref<C: Copy>(&self, repacker: CompilerCtxt<'_, 'tcx, C>) -> Self {
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
    ///
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

    pub fn nearest_owned_place(self, repacker: CompilerCtxt<'_, 'tcx>) -> Self {
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

    pub(crate) fn is_prefix_or_postfix_of(self, other: Self) -> bool {
        self.is_prefix(other) || other.is_prefix(self)
    }

    #[cfg(feature = "debug_info")]
    pub fn debug_info(&self) -> DebugInfo<'static> {
        self.1
    }
}

impl Debug for Place<'_> {
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
                _ => todo!(),
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
                _ => todo!(),
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

impl PartialEq for Place<'_> {
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
    #[cfg(feature = "debug_info")]
    fn from(value: PlaceRef<'tcx>) -> Self {
        Self(value, DebugInfo::new_static())
    }
    #[cfg(not(feature = "debug_info"))]
    fn from(value: PlaceRef<'tcx>) -> Self {
        Self(value)
    }
}
impl<'tcx> From<MirPlace<'tcx>> for Place<'tcx> {
    #[cfg(feature = "debug_info")]
    fn from(value: MirPlace<'tcx>) -> Self {
        Self(value.as_ref(), DebugInfo::new_static())
    }
    #[cfg(not(feature = "debug_info"))]
    fn from(value: MirPlace<'tcx>) -> Self {
        Self(value.as_ref())
    }
}
impl From<Local> for Place<'_> {
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
