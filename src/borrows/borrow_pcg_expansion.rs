use std::collections::BTreeMap;

use itertools::Itertools;
use serde_json::json;

use crate::{
    edgedata_enum,
    rustc_interface::{
        data_structures::fx::FxHashSet,
        middle::{mir::PlaceElem, ty},
        span::Symbol,
        target::abi::FieldIdx,
        target::abi::VariantIdx,
    },
    utils::{CorrectedPlace, HasPlace, Place, PlaceRepacker},
};

use super::{
    borrow_pcg_edge::{BlockingNode, LocalNode, PCGNode},
    domain::{MaybeOldPlace, ToJsonWithRepacker},
    edge_data::EdgeData,
    has_pcs_elem::HasPcsElems,
    region_projection::RegionProjection,
};

/// An expansion of a place in the Borrow PCG, e.g {*x.f} -> {*x.f.a,
/// *x.f.b}
#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct ExpansionOfBorrowed<'tcx, P = LocalNode<'tcx>> {
    pub(crate) base: P,
    expansion: BorrowExpansion<'tcx>,
}

/// The projections resulting from a node in the Borrow PCG.
#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub(crate) enum BorrowExpansion<'tcx> {
    /// Fields from e.g. a struct or tuple, e.g. `{*x.f} -> {*x.f.a, *x.f.b}`
    /// Note that for region projections, not every field of the base type may
    /// be included. For example consider the following:
    /// ```
    /// struct S<'a, 'b> { x: &'a mut i32, y: &'b mut i32 }
    ///
    /// let s: S<'a, 'b> = S { ??? };
    /// ```
    /// The projection of `s↓'a` contains only `{s.x↓'a}` because nothing under
    /// `'a` is accessible via `s.y`.
    Fields(BTreeMap<FieldIdx, ty::Ty<'tcx>>),
    /// A downcast, e.g. `{x} -> {x as Some}` where `x` is of type `Option<T>`
    Downcast(Option<Symbol>, VariantIdx),
    /// A dereference, e.g. {x} -> {*x}
    Deref,
}

impl<'tcx> BorrowExpansion<'tcx> {
    pub(super) fn from_places(
        base_place: Place<'tcx>,
        places: Vec<Place<'tcx>>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Self {
        let place_ty = base_place.ty(repacker);

        // The maximum number of places expected in the expansion, according to
        // the type
        let max_places = match place_ty.ty.kind() {
            ty::TyKind::Adt(adt_def, _) => {
                if adt_def.is_box() {
                    1
                } else if adt_def.is_enum() {
                    place_ty
                        .variant_index
                        .map(|variant_idx| adt_def.variant(variant_idx).fields.len())
                        .unwrap_or(1)
                } else {
                    adt_def.non_enum_variant().fields.len()
                }
            }
            ty::TyKind::Tuple(tys) => tys.len(),
            ty::TyKind::Closure(_, substs) => substs.as_closure().upvar_tys().len(),
            _ => 1,
        };

        assert!(
            places.len() <= max_places,
            "Based on the type {:?}, we expected no more than {} places, but got {} ({:?})",
            place_ty,
            max_places,
            places.len(),
            places
        );

        if max_places > 1 {
            // This is definitely something with multiple fields.
            let fields = places
                .iter()
                .map(
                    |p| match CorrectedPlace::new(*p, repacker).last_projection() {
                        Some(elem) => match *elem {
                            PlaceElem::Field(field_idx, ty) => (field_idx, ty),
                            other => panic!("Expected a field projection, got {:?}", other),
                        },
                        _ => panic!("Expected a field projection"),
                    },
                )
                .collect();
            BorrowExpansion::Fields(fields)
        } else {
            match CorrectedPlace::new(places[0], repacker).last_projection() {
                Some(elem) => match *elem {
                    PlaceElem::Field(field_idx, ty) => {
                        return BorrowExpansion::Fields([(field_idx, ty)].into_iter().collect());
                    }
                    PlaceElem::Deref => {
                        return BorrowExpansion::Deref;
                    }
                    PlaceElem::Downcast(symbol, variant_idx) => {
                        return BorrowExpansion::Downcast(symbol, variant_idx);
                    }
                    other => todo!("{other:?} for type {:?}", place_ty.ty),
                },
                _ => unreachable!(),
            }
        }
    }

    pub(super) fn elems(&self) -> Vec<PlaceElem<'tcx>> {
        match self {
            BorrowExpansion::Fields(fields) => fields
                .iter()
                .sorted_by_key(|(idx, _)| *idx)
                .map(|(idx, ty)| PlaceElem::Field(*idx, *ty))
                .collect(),
            BorrowExpansion::Deref => vec![PlaceElem::Deref],
            BorrowExpansion::Downcast(symbol, variant_idx) => {
                vec![PlaceElem::Downcast(*symbol, *variant_idx)]
            }
        }
    }
}

impl<'tcx, P: HasPlace<'tcx>> ExpansionOfBorrowed<'tcx, P> {
    pub fn expansion(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Vec<P> {
        self.expansion
            .elems()
            .into_iter()
            .map(|p| self.base.project_deeper(repacker, p))
            .collect()
    }
}

impl<'tcx> TryFrom<ExpansionOfBorrowed<'tcx, LocalNode<'tcx>>>
    for ExpansionOfBorrowed<'tcx, MaybeOldPlace<'tcx>>
{
    type Error = ();
    fn try_from(
        expansion: ExpansionOfBorrowed<'tcx, LocalNode<'tcx>>,
    ) -> Result<Self, Self::Error> {
        Ok(ExpansionOfBorrowed {
            base: expansion.base.try_into()?,
            expansion: expansion.expansion,
        })
    }
}

impl<'tcx> HasPcsElems<MaybeOldPlace<'tcx>> for ExpansionOfBorrowed<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        self.base.pcs_elems()
    }
}

impl<'tcx> EdgeData<'tcx> for ExpansionOfBorrowed<'tcx> {
    fn blocked_nodes(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<PCGNode<'tcx>> {
        vec![self.base.into()].into_iter().collect()
    }

    fn blocked_by_nodes(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> FxHashSet<super::borrow_pcg_edge::LocalNode<'tcx>> {
        self.expansion(repacker)
            .into_iter()
            .map(|p| p.into())
            .collect()
    }

    fn is_owned_expansion(&self) -> bool {
        todo!()
    }
}

/// An expansion of a place from the Owned PCG to the Borrow PCG, e.g
/// {x} -> {*x}
#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct ExpansionOfOwned<'tcx> {
    base: MaybeOldPlace<'tcx>,
}

impl<'tcx> EdgeData<'tcx> for ExpansionOfOwned<'tcx> {
    fn blocked_nodes(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> FxHashSet<super::borrow_pcg_edge::PCGNode<'tcx>> {
        let mut blocked_nodes = vec![self.base.into()];
        if self.base.has_region_projections(repacker) {
            blocked_nodes.push(self.base_region_projection(repacker).into());
        }
        blocked_nodes.into_iter().collect()
    }

    fn blocked_by_nodes(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> FxHashSet<super::borrow_pcg_edge::LocalNode<'tcx>> {
        vec![self.expansion(repacker)]
            .into_iter()
            .map(|p| p.into())
            .collect()
    }

    fn is_owned_expansion(&self) -> bool {
        true
    }
}

impl<'tcx> ExpansionOfOwned<'tcx> {
    pub(crate) fn new(base: MaybeOldPlace<'tcx>) -> Self {
        Self { base }
    }

    pub(crate) fn base(&self) -> MaybeOldPlace<'tcx> {
        self.base
    }

    pub(crate) fn expansion(&self, repacker: PlaceRepacker<'_, 'tcx>) -> MaybeOldPlace<'tcx> {
        self.base.project_deref(repacker)
    }

    pub(crate) fn base_region_projection(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> RegionProjection<'tcx, MaybeOldPlace<'tcx>> {
        self.base.region_projection(0, repacker)
    }
}

/// An *expansion* of a place (e.g *x -> {*x.f, *x.g}) or region projection
/// (e.g. {x↓'a} -> {x.f↓'a, x.g↓'a}) where the expanded part is in the Borrow
/// PCG.
#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub enum BorrowPCGExpansion<'tcx, P = LocalNode<'tcx>> {
    /// An expansion of a place from the Free PCG to the Borrow PCG, e.g
    /// {x} -> {*x}
    FromOwned(ExpansionOfOwned<'tcx>),
    /// An expansion of a place in the Borrow PCG, e.g {*x.f} -> {*x.f.a,
    /// *x.f.b}
    FromBorrow(ExpansionOfBorrowed<'tcx, P>),
}

impl<'tcx> TryFrom<BorrowPCGExpansion<'tcx, LocalNode<'tcx>>>
    for BorrowPCGExpansion<'tcx, MaybeOldPlace<'tcx>>
{
    type Error = ();
    fn try_from(expansion: BorrowPCGExpansion<'tcx, LocalNode<'tcx>>) -> Result<Self, Self::Error> {
        match expansion {
            BorrowPCGExpansion::FromOwned(owned) => Ok(BorrowPCGExpansion::FromOwned(owned)),
            BorrowPCGExpansion::FromBorrow(borrowed) => {
                Ok(BorrowPCGExpansion::FromBorrow(borrowed.try_into()?))
            }
        }
    }
}

edgedata_enum!(
    BorrowPCGExpansion<'tcx>,
    FromOwned(OwnedExpansion<'tcx>),
    FromBorrow(BorrowDerefExpansion<'tcx>)
);

impl<'tcx, P: Copy + From<MaybeOldPlace<'tcx>>> BorrowPCGExpansion<'tcx, P> {
    pub fn base(&self) -> P {
        match self {
            BorrowPCGExpansion::FromOwned(owned) => owned.base().into(),
            BorrowPCGExpansion::FromBorrow(e) => e.base,
        }
    }
}

impl<'tcx> HasPcsElems<MaybeOldPlace<'tcx>> for ExpansionOfOwned<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        vec![&mut self.base]
    }
}

impl<'tcx> HasPcsElems<MaybeOldPlace<'tcx>> for BorrowPCGExpansion<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        match self {
            BorrowPCGExpansion::FromOwned(owned) => owned.pcs_elems(),
            BorrowPCGExpansion::FromBorrow(e) => e.pcs_elems(),
        }
    }
}

impl<'tcx, T> HasPcsElems<RegionProjection<'tcx, T>> for BorrowPCGExpansion<'tcx>
where
    BorrowPCGExpansion<'tcx>: HasPcsElems<T>,
{
    fn pcs_elems(&mut self) -> Vec<&mut RegionProjection<'tcx, T>> {
        vec![]
    }
}

impl<'tcx> From<ExpansionOfOwned<'tcx>> for BorrowPCGExpansion<'tcx> {
    fn from(owned: ExpansionOfOwned<'tcx>) -> Self {
        BorrowPCGExpansion::FromOwned(owned)
    }
}

impl<'tcx, P: HasPlace<'tcx> + From<MaybeOldPlace<'tcx>> + PartialEq + Eq + std::hash::Hash>
    BorrowPCGExpansion<'tcx, P>
{
    pub fn expansion(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Vec<P> {
        match self {
            BorrowPCGExpansion::FromOwned(owned) => vec![owned.expansion(repacker).into()],
            BorrowPCGExpansion::FromBorrow(e) => e.expansion(repacker),
        }
    }

    pub fn blocked_by_nodes(&self, repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<P> {
        self.expansion(repacker).into_iter().collect()
    }
}

impl<'tcx, P: HasPlace<'tcx> + std::fmt::Debug + Copy + Into<BlockingNode<'tcx>>>
    BorrowPCGExpansion<'tcx, P>
{
    pub fn is_owned_expansion(&self) -> bool {
        matches!(self, BorrowPCGExpansion::FromOwned { .. })
    }

    pub fn borrow_expansion(&self) -> Option<&ExpansionOfBorrowed<'tcx, P>> {
        match self {
            BorrowPCGExpansion::FromBorrow(e) => Some(e),
            _ => None,
        }
    }

    pub(super) fn new(
        base: P,
        expansion: BorrowExpansion<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Self {
        if let LocalNode::Place(p) = base.into()
            && p.is_owned(repacker)
        {
            assert!(matches!(expansion, BorrowExpansion::Deref));
            BorrowPCGExpansion::FromOwned(ExpansionOfOwned::new(p))
        } else {
            BorrowPCGExpansion::from_borrowed_base(base, expansion, repacker)
        }
    }

    pub(super) fn from_borrowed_base(
        base: P,
        expansion: BorrowExpansion<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Self {
        if let LocalNode::Place(p) = base.into() {
            assert!(!p.is_owned(repacker));
        }
        BorrowPCGExpansion::FromBorrow(ExpansionOfBorrowed { base, expansion })
    }

    pub fn expansion_elems(&self) -> Vec<PlaceElem<'tcx>> {
        match self {
            BorrowPCGExpansion::FromOwned { .. } => vec![PlaceElem::Deref],
            BorrowPCGExpansion::FromBorrow(e) => e.expansion.elems(),
        }
    }
}

impl<'tcx> ToJsonWithRepacker<'tcx> for BorrowPCGExpansion<'tcx> {
    fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        json!({
            "base": self.base().to_json(repacker),
            "expansion": self.expansion(repacker).iter().map(|p| p.to_json(repacker)).collect::<Vec<_>>(),
        })
    }
}
