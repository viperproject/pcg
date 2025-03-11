use std::collections::{BTreeMap, BTreeSet};

use itertools::Itertools;
use serde_json::json;

use super::{
    borrow_pcg_edge::{BlockedNode, BlockingNode, LocalNode},
    edge_data::EdgeData,
    has_pcs_elem::HasPcgElems,
    region_projection::RegionProjection,
};
use crate::utils::json::ToJsonWithRepacker;
use crate::utils::place::maybe_old::MaybeOldPlace;
use crate::{combined_pcs::PcgError, utils::place::corrected::CorrectedPlace};
use crate::{
    combined_pcs::{PCGNode, PCGNodeLike},
    edgedata_enum,
    rustc_interface::{
        data_structures::fx::FxHashSet,
        middle::{
            mir::{Local, PlaceElem},
            ty,
        },
        span::Symbol,
        target::abi::{FieldIdx, VariantIdx},
    },
    utils::{
        display::DisplayWithRepacker, maybe_remote::MaybeRemotePlace, validity::HasValidityCheck,
        ConstantIndex, HasPlace, Place, PlaceRepacker,
    },
};

/// An expansion of a place in the Borrow PCG, e.g {*x.f} -> {*x.f.a,
/// *x.f.b}
#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct ExpansionOfBorrowed<'tcx, P = LocalNode<'tcx>> {
    pub(crate) base: P,
    pub(crate) expansion: PlaceExpansion<'tcx>,
}

impl<'tcx, P: PCGNodeLike<'tcx> + HasPlace<'tcx>> DisplayWithRepacker<'tcx>
    for ExpansionOfBorrowed<'tcx, P>
{
    fn to_short_string(&self, repacker: PlaceRepacker<'_, 'tcx>) -> String {
        let expansion_set: Vec<String> = self
            .expansion(repacker)
            .unwrap()
            .into_iter()
            .map(|place| place.to_short_string(repacker))
            .collect();
        format!(
            "{{{}}} -> {{{}}}",
            self.base.to_short_string(repacker),
            expansion_set.join(", ")
        )
    }
}

impl<'tcx, P: HasValidityCheck<'tcx>> HasValidityCheck<'tcx> for ExpansionOfBorrowed<'tcx, P> {
    fn check_validity(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Result<(), String> {
        self.base.check_validity(repacker)?;
        self.expansion.check_validity(repacker)
    }
}
/// The projections resulting from an expansion of a place.
///
/// This representation is preferred to a `Vec<PlaceElem>` because it ensures
/// it enables a more reasonable notion of equality between expansions. Directly
/// storing the place elements in a `Vec` could lead to different representations
/// for the same expansion, e.g. `{*x.f.a, *x.f.b}` and `{*x.f.b, *x.f.a}`.
#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub(crate) enum PlaceExpansion<'tcx> {
    /// Fields from e.g. a struct or tuple, e.g. `{*x.f} -> {*x.f.a, *x.f.b}`
    /// Note that for region projections, not every field of the base type may
    /// be included. For example consider the following:
    /// ```ignore
    /// struct S<'a, 'b> { x: &'a mut i32, y: &'b mut i32 }
    ///
    /// let s: S<'a, 'b> = S { x: &mut 1, y: &mut 2 };
    /// ```
    /// The projection of `s↓'a` contains only `{s.x↓'a}` because nothing under
    /// `'a` is accessible via `s.y`.
    Fields(BTreeMap<FieldIdx, ty::Ty<'tcx>>),
    /// See [`PlaceElem::Downcast`]
    Downcast(Option<Symbol>, VariantIdx),
    /// See [`PlaceElem::Deref`]
    Deref,
    /// See [`PlaceElem::Index`]
    Index(Local),
    /// See [`PlaceElem::ConstantIndex`]
    ConstantIndices(BTreeSet<ConstantIndex>),
    /// See [`PlaceElem::Subslice`]
    Subslice { from: u64, to: u64, from_end: bool },
}

impl<'tcx> HasValidityCheck<'tcx> for PlaceExpansion<'tcx> {
    fn check_validity(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> Result<(), String> {
        Ok(())
    }
}

impl<'tcx> PlaceExpansion<'tcx> {
    #[allow(unused)]
    pub(crate) fn is_deref(&self) -> bool {
        matches!(self, PlaceExpansion::Deref)
    }

    pub(crate) fn from_places(places: Vec<Place<'tcx>>, repacker: PlaceRepacker<'_, 'tcx>) -> Self {
        let mut fields = BTreeMap::new();
        let mut constant_indices = BTreeSet::new();

        for place in places {
            let corrected_place = CorrectedPlace::new(place, repacker);
            let last_projection = corrected_place.last_projection();
            if let Some(elem) = last_projection {
                match *elem {
                    PlaceElem::Field(field_idx, ty) => {
                        fields.insert(field_idx, ty);
                    }
                    PlaceElem::ConstantIndex {
                        offset,
                        min_length,
                        from_end,
                    } => {
                        constant_indices.insert(ConstantIndex {
                            offset,
                            min_length,
                            from_end,
                        });
                    }
                    PlaceElem::Deref => return PlaceExpansion::Deref,
                    PlaceElem::Downcast(symbol, variant_idx) => {
                        return PlaceExpansion::Downcast(symbol, variant_idx);
                    }
                    PlaceElem::Index(idx) => {
                        return PlaceExpansion::Index(idx);
                    }
                    PlaceElem::Subslice { from, to, from_end } => {
                        return PlaceExpansion::Subslice { from, to, from_end };
                    }
                    PlaceElem::OpaqueCast(_) => todo!(),
                    PlaceElem::Subtype(_) => todo!(),
                }
            }
        }

        if !fields.is_empty() {
            assert!(constant_indices.is_empty());
            PlaceExpansion::Fields(fields)
        } else if !constant_indices.is_empty() {
            PlaceExpansion::ConstantIndices(constant_indices)
        } else {
            unreachable!()
        }
    }

    pub(crate) fn elems(&self) -> Vec<PlaceElem<'tcx>> {
        match self {
            PlaceExpansion::Fields(fields) => {
                assert!(fields.len() <= 1024, "Too many fields: {:?}", fields);
                fields
                    .iter()
                    .sorted_by_key(|(idx, _)| *idx)
                    .map(|(idx, ty)| PlaceElem::Field(*idx, *ty))
                    .collect()
            }
            PlaceExpansion::Deref => vec![PlaceElem::Deref],
            PlaceExpansion::Downcast(symbol, variant_idx) => {
                vec![PlaceElem::Downcast(*symbol, *variant_idx)]
            }
            PlaceExpansion::Index(idx) => vec![PlaceElem::Index(*idx)],
            PlaceExpansion::ConstantIndices(constant_indices) => constant_indices
                .iter()
                .sorted_by_key(|a| a.offset)
                .map(|c| PlaceElem::ConstantIndex {
                    offset: c.offset,
                    min_length: c.min_length,
                    from_end: c.from_end,
                })
                .collect(),
            PlaceExpansion::Subslice { from, to, from_end } => {
                vec![PlaceElem::Subslice {
                    from: *from,
                    to: *to,
                    from_end: *from_end,
                }]
            }
        }
    }
}

impl<P: Copy> ExpansionOfBorrowed<'_, P> {
    pub fn base(&self) -> P {
        self.base
    }
}

impl<'tcx, P: PCGNodeLike<'tcx> + HasPlace<'tcx>> ExpansionOfBorrowed<'tcx, P> {
    pub fn expansion<'slf>(
        &'slf self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Result<Vec<P>, PcgError> {
        self.expansion
            .elems()
            .into_iter()
            .map(move |p| self.base.project_deeper(p, repacker))
            .collect::<Result<Vec<_>, _>>()
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

impl<'tcx> HasPcgElems<MaybeOldPlace<'tcx>> for ExpansionOfBorrowed<'tcx> {
    fn pcg_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        self.base.pcg_elems()
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
        self.expansion(repacker).unwrap().into_iter().collect()
    }

    fn is_owned_expansion(&self) -> bool {
        false
    }

    fn blocks_node(&self, node: BlockedNode<'tcx>, repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        if let Some(local) = node.as_local_node(repacker) {
            self.base == local
        } else {
            false
        }
    }

    fn is_blocked_by(&self, node: LocalNode<'tcx>, repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        match (self.base, node) {
            (PCGNode::Place(p1), PCGNode::Place(p2)) => {
                if let Some((node_prefix, last_proj)) = p2.last_projection()
                    && node_prefix == p1
                {
                    self.expansion.elems().contains(&last_proj)
                } else {
                    false
                }
            }
            (PCGNode::RegionProjection(rp1), PCGNode::RegionProjection(rp2)) => {
                if let Some((node_prefix, last_proj)) = rp2.base().last_projection()
                    && node_prefix == rp1.base()
                {
                    self.expansion.elems().contains(&last_proj)
                        && rp1.region(repacker) == rp2.region(repacker)
                } else {
                    false
                }
            }
            _ => false,
        }
    }
}

/// An expansion of a place from the Owned PCG to the Borrow PCG, e.g
/// {x} -> {*x}
#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct ExpansionOfOwned<'tcx> {
    base: MaybeOldPlace<'tcx>,
}

impl<'tcx> DisplayWithRepacker<'tcx> for ExpansionOfOwned<'tcx> {
    fn to_short_string(&self, repacker: PlaceRepacker<'_, 'tcx>) -> String {
        format!(
            "{{{}}} -> {{*{}}}",
            self.base.to_short_string(repacker),
            self.base.to_short_string(repacker)
        )
    }
}

impl<'tcx> HasValidityCheck<'tcx> for ExpansionOfOwned<'tcx> {
    fn check_validity(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> Result<(), String> {
        Ok(())
    }
}

impl<'tcx> EdgeData<'tcx> for ExpansionOfOwned<'tcx> {
    fn blocks_node(&self, node: BlockedNode<'tcx>, _repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        match node {
            PCGNode::Place(MaybeRemotePlace::Local(p)) => self.base == p,
            // We block all the region projections of this place, so it's only necessary to compare the base
            PCGNode::RegionProjection(p) => p.base() == self.base.into(),
            _ => false,
        }
    }

    fn blocked_nodes(&self, repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<PCGNode<'tcx>> {
        let mut blocked_nodes = vec![self.base.into()];
        for rp in self.base.region_projections(repacker) {
            blocked_nodes.push(rp.to_pcg_node(repacker));
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
    FromOwned(ExpansionOfOwned<'tcx>),
    FromBorrow(ExpansionOfBorrowed<'tcx>)
);

impl<'tcx, P: PCGNodeLike<'tcx> + From<MaybeOldPlace<'tcx>>> BorrowPCGExpansion<'tcx, P> {
    pub fn base(&self) -> P {
        match self {
            BorrowPCGExpansion::FromOwned(owned) => owned.base().into(),
            BorrowPCGExpansion::FromBorrow(e) => e.base,
        }
    }
}

impl<'tcx> HasPcgElems<MaybeOldPlace<'tcx>> for ExpansionOfOwned<'tcx> {
    fn pcg_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        vec![&mut self.base]
    }
}

impl<'tcx, T> HasPcgElems<RegionProjection<'tcx, T>> for BorrowPCGExpansion<'tcx>
where
    BorrowPCGExpansion<'tcx>: HasPcgElems<T>,
{
    fn pcg_elems(&mut self) -> Vec<&mut RegionProjection<'tcx, T>> {
        vec![]
    }
}

impl<'tcx, P: HasPlace<'tcx> + From<MaybeOldPlace<'tcx>> + PCGNodeLike<'tcx>>
    BorrowPCGExpansion<'tcx, P>
{
    pub fn expansion(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Result<Vec<P>, PcgError> {
        match self {
            BorrowPCGExpansion::FromOwned(owned) => Ok(vec![owned.expansion(repacker).into()]),
            BorrowPCGExpansion::FromBorrow(e) => e.expansion(repacker),
        }
    }
}

impl<'tcx, P: PCGNodeLike<'tcx> + HasPlace<'tcx> + Into<BlockingNode<'tcx>>>
    BorrowPCGExpansion<'tcx, P>
{
    pub(crate) fn is_deref_of_borrow(&self, repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        match self {
            BorrowPCGExpansion::FromOwned(_) => true,
            BorrowPCGExpansion::FromBorrow(e) => match e.base.into() {
                BlockingNode::Place(p) => p.ty(repacker).ty.is_ref(),
                BlockingNode::RegionProjection(_) => false,
            },
        }
    }

    pub(crate) fn is_owned_expansion(&self) -> bool {
        matches!(self, BorrowPCGExpansion::FromOwned { .. })
    }

    pub(super) fn new(
        base: P,
        expansion: PlaceExpansion<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Result<Self, PcgError> {
        if let LocalNode::Place(p) = base.into()
            && p.is_owned(repacker)
        {
            assert!(
                matches!(expansion, PlaceExpansion::Deref),
                "Unexpected expansion for {:?}: {:?}",
                base,
                expansion
            );
            Ok(BorrowPCGExpansion::FromOwned(ExpansionOfOwned::new(p)))
        } else {
            BorrowPCGExpansion::from_borrowed_base(base, expansion, repacker)
        }
    }

    pub(super) fn from_borrowed_base(
        base: P,
        expansion: PlaceExpansion<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Result<Self, PcgError> {
        if let LocalNode::Place(p) = base.into() {
            assert!(!p.is_owned(repacker));
        }
        let borrow_expansion = ExpansionOfBorrowed { base, expansion };
        if let Err(e) = borrow_expansion.expansion(repacker) {
            Err(e)
        } else {
            Ok(BorrowPCGExpansion::FromBorrow(borrow_expansion))
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
