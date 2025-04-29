use std::{
    collections::{BTreeMap, BTreeSet},
    marker::PhantomData,
};

use itertools::Itertools;
use serde_json::json;

use super::{
    borrow_pcg_edge::{BlockedNode, BlockingNode, LocalNode},
    edge_data::EdgeData,
    has_pcs_elem::{HasPcgElems, LabelRegionProjection, MakePlaceOld},
    latest::Latest,
    region_projection::{RegionProjection, RegionProjectionLabel},
};
use crate::utils::json::ToJsonWithCompilerCtxt;
use crate::utils::place::maybe_old::MaybeOldPlace;
use crate::{pcg::PcgError, utils::place::corrected::CorrectedPlace};
use crate::{
    pcg::{PCGNode, PCGNodeLike},
    rustc_interface::{
        data_structures::fx::FxHashSet,
        middle::{
            mir::{Local, Location, PlaceElem},
            ty,
        },
        span::Symbol,
        target::abi::{FieldIdx, VariantIdx},
    },
    utils::{
        display::DisplayWithCompilerCtxt, validity::HasValidityCheck, CompilerCtxt, ConstantIndex,
        HasPlace, Place,
    },
};

/// The projections resulting from an expansion of a place.
///
/// This representation is preferred to a `Vec<PlaceElem>` because it ensures
/// it enables a more reasonable notion of equality between expansions. Directly
/// storing the place elements in a `Vec` could lead to different representations
/// for the same expansion, e.g. `{*x.f.a, *x.f.b}` and `{*x.f.b, *x.f.a}`.
#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub enum PlaceExpansion<'tcx> {
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
    fn check_validity<C: Copy>(&self, _repacker: CompilerCtxt<'_, 'tcx, C>) -> Result<(), String> {
        Ok(())
    }
}

impl<'tcx> PlaceExpansion<'tcx> {
    #[allow(unused)]
    pub(crate) fn is_deref(&self) -> bool {
        matches!(self, PlaceExpansion::Deref)
    }

    pub(crate) fn from_places(places: Vec<Place<'tcx>>, repacker: CompilerCtxt<'_, 'tcx>) -> Self {
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
            PlaceExpansion::Fields(fields) => fields
                .iter()
                .sorted_by_key(|(idx, _)| *idx)
                .map(|(idx, ty)| PlaceElem::Field(*idx, *ty))
                .collect(),
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

/// An *expansion* of a place (e.g *x -> {*x.f, *x.g}) or region projection
/// (e.g. {x↓'a} -> {x.f↓'a, x.g↓'a}) where the expanded part is in the Borrow
/// PCG.
#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct BorrowPCGExpansion<'tcx, P = LocalNode<'tcx>> {
    pub(crate) base: P,
    pub(crate) expansion: Vec<P>,
    /// If this expansion is a deref, this is the label associated with the
    /// region projection. This label must be None if:
    /// - The place of `base` is not a mutable reference, or
    /// - `expansion` does not contain any region projections, or
    /// - this deref is for a shared borrow / read access
    deref_blocked_region_projection_label: Option<RegionProjectionLabel>,
    _marker: PhantomData<&'tcx ()>,
}

impl<'tcx> BorrowPCGExpansion<'tcx> {
    fn is_mutable_deref_of_place_with_nested_region_projections(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        let place = self.base.place();
        place.is_mut_ref(ctxt) && place.contains_mutable_region_projections(ctxt)
    }
}

impl<'tcx> LabelRegionProjection<'tcx> for BorrowPCGExpansion<'tcx> {
    fn label_region_projection(
        &mut self,
        projection: &RegionProjection<'tcx, MaybeOldPlace<'tcx>>,
        label: Option<RegionProjectionLabel>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        let mut changed = self
            .base
            .label_region_projection(projection, label, repacker);
        for p in &mut self.expansion {
            changed |= p.label_region_projection(projection, label, repacker);
        }
        if self.is_mutable_deref_of_place_with_nested_region_projections(repacker)
            && projection.label == self.deref_blocked_region_projection_label
        {
            self.deref_blocked_region_projection_label = label;
        }
        changed
    }
}

impl<'tcx> MakePlaceOld<'tcx> for BorrowPCGExpansion<'tcx> {
    fn make_place_old(
        &mut self,
        place: Place<'tcx>,
        latest: &Latest<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        let mut changed = self.base.make_place_old(place, latest, repacker);
        self.expansion.iter_mut().for_each(|p| {
            changed |= p.make_place_old(place, latest, repacker);
        });
        changed
    }
}

impl<'tcx> DisplayWithCompilerCtxt<'tcx> for BorrowPCGExpansion<'tcx> {
    fn to_short_string(&self, repacker: CompilerCtxt<'_, 'tcx>) -> String {
        format!(
            "{{{}}} -> {{{}}}",
            self.base.to_short_string(repacker),
            self.expansion
                .iter()
                .map(|p| p.to_short_string(repacker))
                .join(", ")
        )
    }
}

impl<'tcx> HasValidityCheck<'tcx> for BorrowPCGExpansion<'tcx> {
    fn check_validity<C: Copy>(&self, _repacker: CompilerCtxt<'_, 'tcx, C>) -> Result<(), String> {
        Ok(())
    }
}

impl<'tcx> EdgeData<'tcx> for BorrowPCGExpansion<'tcx> {
    fn blocks_node<C: Copy>(
        &self,
        node: BlockedNode<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> bool {
        if self.base.to_pcg_node(repacker) == node {
            return true;
        }
        if let Some(blocked_rp) = self.deref_blocked_region_projection(repacker) {
            node == blocked_rp
        } else {
            false
        }
    }

    fn blocked_nodes<C: Copy>(
        &self,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> FxHashSet<PCGNode<'tcx>> {
        let mut base: FxHashSet<PCGNode<'tcx>> = vec![self.base.into()].into_iter().collect();
        if let Some(blocked_rp) = self.deref_blocked_region_projection(repacker) {
            base.insert(blocked_rp);
        }
        base
    }

    fn blocked_by_nodes<C: Copy>(
        &self,
        _repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> FxHashSet<LocalNode<'tcx>> {
        self.expansion.iter().copied().collect()
    }
}

impl<'tcx> TryFrom<BorrowPCGExpansion<'tcx, LocalNode<'tcx>>>
    for BorrowPCGExpansion<'tcx, MaybeOldPlace<'tcx>>
{
    type Error = ();
    fn try_from(expansion: BorrowPCGExpansion<'tcx, LocalNode<'tcx>>) -> Result<Self, Self::Error> {
        Ok(BorrowPCGExpansion {
            base: expansion.base.try_into()?,
            deref_blocked_region_projection_label: expansion.deref_blocked_region_projection_label,
            expansion: expansion
                .expansion
                .into_iter()
                .map(|p| p.try_into())
                .collect::<Result<Vec<_>, _>>()?,
            _marker: PhantomData,
        })
    }
}

impl<'tcx> HasPcgElems<MaybeOldPlace<'tcx>> for BorrowPCGExpansion<'tcx> {
    fn pcg_elems(&mut self) -> Vec<&mut MaybeOldPlace<'tcx>> {
        let mut elems = self.base.pcg_elems();
        elems.extend(self.expansion.iter_mut().flat_map(|p| p.pcg_elems()));
        elems
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

impl<'tcx> BorrowPCGExpansion<'tcx> {
    pub(crate) fn is_deref<C: Copy>(&self, repacker: CompilerCtxt<'_, 'tcx, C>) -> bool {
        if let BlockingNode::Place(p) = self.base {
            p.place().is_ref(repacker)
        } else {
            false
        }
    }

    pub(crate) fn deref_blocked_region_projection<C: Copy>(
        &self,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> Option<PCGNode<'tcx>> {
        if let BlockingNode::Place(p) = self.base
            && let Some(mut projection) = p.base_region_projection(repacker)
        {
            projection.label = self.deref_blocked_region_projection_label;
            Some(projection.into())
        } else {
            None
        }
    }
}

impl<'tcx, P: PCGNodeLike<'tcx> + HasPlace<'tcx> + Into<BlockingNode<'tcx>>>
    BorrowPCGExpansion<'tcx, P>
{
    pub fn base(&self) -> P {
        self.base
    }

    pub fn expansion(&self) -> &[P] {
        &self.expansion
    }

    pub(crate) fn is_owned_expansion(&self, repacker: CompilerCtxt<'_, 'tcx>) -> bool {
        match self.base.into() {
            BlockingNode::Place(p) => p.is_owned(repacker),
            BlockingNode::RegionProjection(_) => false,
        }
    }

    pub(super) fn new(
        base: P,
        expansion: PlaceExpansion<'tcx>,
        location: Location,
        for_exclusive: bool,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<Self, PcgError>
    where
        P: Ord + HasPlace<'tcx>,
    {
        let deref_blocked_region_projection_label = if for_exclusive
            && base.place().is_mut_ref(ctxt)
            && base.place().contains_mutable_region_projections(ctxt)
        {
            Some(location.into())
        } else {
            None
        };
        Ok(Self {
            base,
            expansion: expansion
                .elems()
                .into_iter()
                .map(|elem| base.project_deeper(elem, ctxt))
                .collect::<Result<Vec<_>, _>>()?,
            deref_blocked_region_projection_label,
            _marker: PhantomData,
        })
    }
}

impl<'tcx> ToJsonWithCompilerCtxt<'tcx> for BorrowPCGExpansion<'tcx> {
    fn to_json(&self, repacker: CompilerCtxt<'_, 'tcx>) -> serde_json::Value {
        json!({
            "base": self.base.to_json(repacker),
            "expansion": self.expansion.iter().map(|p| p.to_json(repacker)).collect::<Vec<_>>(),
        })
    }
}
