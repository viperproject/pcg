//! Definition of expansion edges in the Borrow PCG.
use std::{collections::BTreeMap, hash::Hash, marker::PhantomData};

use derive_more::From;
use itertools::Itertools;
use serde_json::json;

use super::{
    borrow_pcg_edge::{BlockedNode, BlockingNode, LocalNode},
    edge_data::EdgeData,
    has_pcs_elem::{HasPcgElems, LabelLifetimeProjection, LabelPlace},
    region_projection::{LifetimeProjection, LifetimeProjectionLabel},
};
use crate::{
    borrow_checker::BorrowCheckerInterface,
    borrow_pcg::{
        edge_data::{LabelEdgePlaces, LabelPlacePredicate},
        has_pcs_elem::{
            LabelLifetimeProjectionPredicate, LabelLifetimeProjectionResult, LabelNodeContext,
            LabelPlaceWithContext, PlaceLabeller,
        },
        region_projection::LocalLifetimeProjection,
    },
    free_pcs::{CapabilityKind, RepackGuide},
    pcg::{
        MaybeHasLocation, PcgUnsupportedError,
        obtain::ObtainType,
        place_capabilities::{BlockType, PlaceCapabilities, PlaceCapabilitiesInterface},
    },
    utils::{SnapshotLocation, json::ToJsonWithCompilerCtxt},
};
use crate::{pcg::PcgError, utils::place::corrected::CorrectedPlace};
use crate::{
    pcg::{PCGNode, PCGNodeLike},
    rustc_interface::middle::{mir::PlaceElem, ty},
    utils::{
        CompilerCtxt, HasPlace, Place, display::DisplayWithCompilerCtxt, validity::HasValidityCheck,
    },
};
use crate::{rustc_interface::FieldIdx, utils::place::maybe_old::MaybeLabelledPlace};

/// The projections resulting from an expansion of a place.
///
/// This representation is preferred to a `Vec<PlaceElem>` because it ensures
/// it enables a more reasonable notion of equality between expansions. Directly
/// storing the place elements in a `Vec` could lead to different representations
/// for the same expansion, e.g. `{*x.f.a, *x.f.b}` and `{*x.f.b, *x.f.a}`.
#[derive(PartialEq, Eq, Clone, Debug, Hash, From)]
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
    /// See [`PlaceElem::Deref`]
    Deref,
    Guided(RepackGuide),
}

impl<'tcx> HasValidityCheck<'tcx> for PlaceExpansion<'tcx> {
    fn check_validity(&self, _ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        Ok(())
    }
}

impl<'tcx> PlaceExpansion<'tcx> {
    pub(crate) fn block_type(
        &self,
        base_place: Place<'tcx>,
        obtain_type: ObtainType,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> BlockType {
        if matches!(
            obtain_type,
            ObtainType::TwoPhaseExpand | ObtainType::Capability(CapabilityKind::Read)
        ) {
            BlockType::Read
        } else if matches!(self, PlaceExpansion::Deref) {
            if base_place.is_shared_ref(ctxt) || base_place.projects_shared_ref(ctxt) {
                BlockType::Read
            } else if base_place.is_mut_ref(ctxt) {
                BlockType::DerefRefExclusive
            } else {
                BlockType::Other
            }
        } else {
            BlockType::Other
        }
    }
    pub(crate) fn guide(&self) -> Option<RepackGuide> {
        match self {
            PlaceExpansion::Guided(guide) => Some(*guide),
            _ => None,
        }
    }

    pub(crate) fn from_places(places: Vec<Place<'tcx>>, repacker: CompilerCtxt<'_, 'tcx>) -> Self {
        let mut fields = BTreeMap::new();

        for place in places {
            let corrected_place = CorrectedPlace::new(place, repacker);
            let last_projection = corrected_place.last_projection();
            if let Some(elem) = last_projection {
                match *elem {
                    PlaceElem::Field(field_idx, ty) => {
                        fields.insert(field_idx, ty);
                    }
                    PlaceElem::Deref => return PlaceExpansion::Deref,
                    other => {
                        let repack_guide: RepackGuide = other
                            .try_into()
                            .unwrap_or_else(|_| todo!("unsupported place elem: {:?}", other));
                        return PlaceExpansion::Guided(repack_guide);
                    }
                }
            }
        }

        if !fields.is_empty() {
            PlaceExpansion::Fields(fields)
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
            PlaceExpansion::Guided(guided) => vec![(*guided).into()],
        }
    }
}

/// An *expansion* of a place (e.g *x -> {*x.f, *x.g}) or region projection
/// (e.g. {x↓'a} -> {x.f↓'a, x.g↓'a}) where the expanded part is in the Borrow
/// PCG.
#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct BorrowPcgExpansion<'tcx, P = LocalNode<'tcx>> {
    pub(crate) base: P,
    pub(crate) expansion: Vec<P>,
    /// If this expansion is a deref, this is the label associated with the
    /// region projection. This label must be None if:
    /// - The place of `base` is not a mutable reference, or
    /// - `expansion` does not contain any region projections, or
    /// - this deref is for a shared borrow / read access
    deref_rp_label: Option<LifetimeProjectionLabel>,
    _marker: PhantomData<&'tcx ()>,
}

impl<'tcx> LabelEdgePlaces<'tcx> for BorrowPcgExpansion<'tcx> {
    fn label_blocked_places(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        tracing::debug!(
            "label blocked places: {} with {:?}",
            self.to_short_string(ctxt),
            predicate
        );
        let result =
            self.base
                .label_place_with_context(predicate, labeller, LabelNodeContext::Other, ctxt);
        self.assert_validity(ctxt);
        result
    }

    fn label_blocked_by_places(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        let mut changed = false;
        for p in &mut self.expansion {
            changed |= p.label_place_with_context(
                predicate,
                labeller,
                LabelNodeContext::TargetOfExpansion,
                ctxt,
            );
        }
        self.assert_validity(ctxt);
        changed
    }
}

impl<'tcx> LabelLifetimeProjection<'tcx> for BorrowPcgExpansion<'tcx> {
    fn label_lifetime_projection(
        &mut self,
        predicate: &LabelLifetimeProjectionPredicate<'tcx>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> LabelLifetimeProjectionResult {
        let mut changed = self.base.label_lifetime_projection(predicate, label, ctxt);
        for p in &mut self.expansion {
            changed |= p.label_lifetime_projection(predicate, label, ctxt);
        }
        if let Some(rp) = self.deref_blocked_region_projection(ctxt)
            && predicate.matches(rp.into(), ctxt)
        {
            self.deref_rp_label = label;
        }
        self.assert_validity(ctxt);
        changed
    }
}

impl<'tcx, 'a, P: DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>>
    DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>
    for BorrowPcgExpansion<'tcx, P>
{
    fn to_short_string(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    ) -> String {
        format!(
            "{{{}}} -> {{{}}}",
            self.base.to_short_string(ctxt),
            self.expansion
                .iter()
                .map(|p| p.to_short_string(ctxt))
                .join(", ")
        )
    }
}

impl<'tcx, P: PCGNodeLike<'tcx>> HasValidityCheck<'tcx> for BorrowPcgExpansion<'tcx, P> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        if self.expansion.contains(&self.base) {
            return Err(format!("expansion contains base: {:?}", self));
        }
        for p in &self.expansion {
            if let Some(node) = p.try_to_local_node(ctxt) {
                if node.is_place() && node.place().is_owned(ctxt) {
                    return Err(format!(
                        "Expansion of {:?} contains owned place {}",
                        self,
                        node.place().to_short_string(ctxt)
                    ));
                }
            }
        }
        Ok(())
    }
}

impl<'tcx> EdgeData<'tcx> for BorrowPcgExpansion<'tcx> {
    fn blocks_node<'slf>(&self, node: BlockedNode<'tcx>, repacker: CompilerCtxt<'_, 'tcx>) -> bool {
        if self.base.to_pcg_node(repacker) == node {
            return true;
        }
        if let Some(blocked_rp) = self.deref_blocked_region_projection(repacker) {
            node == blocked_rp.into()
        } else {
            false
        }
    }

    // `return` is needed because both branches have different types
    #[allow(clippy::needless_return)]
    fn blocked_nodes<'slf, BC: Copy>(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, BC>,
    ) -> Box<dyn std::iter::Iterator<Item = PCGNode<'tcx>> + 'slf>
    where
        'tcx: 'slf,
    {
        let iter = std::iter::once(self.base.into());
        if let Some(blocked_rp) = self.deref_blocked_region_projection(ctxt) {
            return Box::new(iter.chain(std::iter::once(blocked_rp.into())));
        } else {
            return Box::new(iter);
        }
    }

    fn blocked_by_nodes<'slf, 'mir: 'slf, BC: Copy>(
        &'slf self,
        _ctxt: CompilerCtxt<'mir, 'tcx, BC>,
    ) -> Box<dyn std::iter::Iterator<Item = LocalNode<'tcx>> + 'slf>
    where
        'tcx: 'mir,
    {
        Box::new(self.expansion.iter().copied())
    }
}

impl<'tcx> TryFrom<BorrowPcgExpansion<'tcx, LocalNode<'tcx>>>
    for BorrowPcgExpansion<'tcx, MaybeLabelledPlace<'tcx>>
{
    type Error = ();
    fn try_from(expansion: BorrowPcgExpansion<'tcx, LocalNode<'tcx>>) -> Result<Self, Self::Error> {
        Ok(BorrowPcgExpansion {
            base: expansion.base.try_into()?,
            deref_rp_label: expansion.deref_rp_label,
            expansion: expansion
                .expansion
                .into_iter()
                .map(|p| p.try_into())
                .collect::<Result<Vec<_>, _>>()?,
            _marker: PhantomData,
        })
    }
}

impl<'tcx> HasPcgElems<MaybeLabelledPlace<'tcx>> for BorrowPcgExpansion<'tcx> {
    fn pcg_elems(&mut self) -> Vec<&mut MaybeLabelledPlace<'tcx>> {
        let mut elems = self.base.pcg_elems();
        elems.extend(self.expansion.iter_mut().flat_map(|p| p.pcg_elems()));
        elems
    }
}

impl<'tcx, T> HasPcgElems<LifetimeProjection<'tcx, T>> for BorrowPcgExpansion<'tcx>
where
    BorrowPcgExpansion<'tcx>: HasPcgElems<T>,
{
    fn pcg_elems(&mut self) -> Vec<&mut LifetimeProjection<'tcx, T>> {
        vec![]
    }
}

impl<'tcx> BorrowPcgExpansion<'tcx> {
    pub(crate) fn is_deref<C: Copy>(&self, repacker: CompilerCtxt<'_, 'tcx, C>) -> bool {
        if let BlockingNode::Place(p) = self.base {
            p.place().is_ref(repacker)
        } else {
            false
        }
    }

    /// If this expansion is a dereference of a place `p`, this returns the
    /// source lifetime projection of this edge For example if this is a shared
    /// reference , it could be an unlabelled lifetime projection e.g. p|'a For
    /// a mutable reference, this will be labelled with the location of the
    /// dereference (e.g p|'a@l),
    pub(crate) fn deref_blocked_region_projection<BC: Copy>(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, BC>,
    ) -> Option<LocalLifetimeProjection<'tcx>> {
        if let BlockingNode::Place(p) = self.base
            && let Some(projection) = p.base_region_projection(ctxt)
        {
            if let Some(SnapshotLocation::BeforeRefReassignment(_)) = p.location() {
                // This is somewhat of a hack to support the following kind of scenario:
                //
                //  - `s` is to be re-assigned or borrowed mutably at location `l`
                //  - `s.f` is shared a reference with lifetime 'a reborrowed into `x`
                //
                // We want to keep the edge {s.f@l, s.f|'a@l} -> {*s.f@l} in the graph
                // Note that s.f|'a@l will be connected to the snapshot of
                // `s|'a@l` (otherwise it would be disconnected from the graph)
                //
                // But in general the snapshot of the place in the places and
                // the lifetime projection are the same, so using the normal
                // logic we couldn't have refer to s.f@l in the place and s.f in
                // the lifetime projection. Therefore we have this special case.
                Some(
                    projection
                        .with_label(self.deref_rp_label, ctxt)
                        .with_base(p.place().into()),
                )
            } else {
                Some(projection.with_label(self.deref_rp_label, ctxt))
            }
        } else {
            None
        }
    }

    /// If this expansion is a dereference of a place `p`, this returns the
    /// dereferenced place `*p`.
    ///
    /// Note that this node is NOT necessary the target node of the graph,
    /// in particular, the target node might be labelled
    pub(crate) fn deref_of_blocked_place(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Option<Place<'tcx>> {
        if let BlockingNode::Place(MaybeLabelledPlace::Current(place)) = self.base
            && place.is_ref(ctxt)
        {
            Some(place.project_deref(ctxt))
        } else {
            None
        }
    }

    /// Returns true iff the expansion is packable, i.e. without losing any
    /// information. This is the case when the expansion node labels (for
    /// places, and for region projections) are the same as the base node
    /// labels.
    pub(crate) fn is_packable(&self, capabilities: &PlaceCapabilities<'tcx>) -> bool {
        match self.base {
            PCGNode::Place(base_place) => {
                let mut fst_cap = None;
                self.expansion.iter().all(|p| {
                    if let PCGNode::Place(MaybeLabelledPlace::Current(place)) = p {
                        if let Some(cap) = fst_cap {
                            if cap != capabilities.get(*place) {
                                return false;
                            }
                        } else {
                            fst_cap = Some(capabilities.get(*place));
                        }
                    }
                    base_place.place().is_prefix_exact(p.place())
                        && p.location() == base_place.location()
                })
            }
            PCGNode::LifetimeProjection(base_rp) => self.expansion.iter().all(|p| {
                if let PCGNode::LifetimeProjection(p_rp) = p {
                    p_rp.place().location() == base_rp.place().location()
                        && base_rp
                            .place()
                            .place()
                            .is_prefix_exact(p_rp.place().place())
                        && p_rp.label() == base_rp.label()
                } else {
                    false
                }
            }),
        }
    }
}

impl<'tcx, P: PCGNodeLike<'tcx> + HasPlace<'tcx> + Into<BlockingNode<'tcx>>>
    BorrowPcgExpansion<'tcx, P>
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
            BlockingNode::LifetimeProjection(_) => false,
        }
    }

    pub(crate) fn new(
        base: P,
        expansion: PlaceExpansion<'tcx>,
        deref_blocked_region_projection_label: Option<LifetimeProjectionLabel>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<Self, PcgError>
    where
        P: Ord + HasPlace<'tcx>,
    {
        let place_ty = base.place().ty(ctxt);
        #[rustversion::before(2025-04-01)]
        let is_raw_ptr = place_ty.ty.is_unsafe_ptr();
        #[rustversion::since(2025-04-01)]
        let is_raw_ptr = place_ty.ty.is_raw_ptr();
        if is_raw_ptr {
            return Err(PcgUnsupportedError::DerefUnsafePtr.into());
        }
        let result = Self {
            base,
            expansion: expansion
                .elems()
                .into_iter()
                .map(|elem| base.project_deeper(elem, ctxt))
                .collect::<Result<Vec<_>, _>>()?,
            deref_rp_label: deref_blocked_region_projection_label,
            _marker: PhantomData,
        };
        result.assert_validity(ctxt);
        Ok(result)
    }
}

impl<'tcx, BC: Copy> ToJsonWithCompilerCtxt<'tcx, BC> for BorrowPcgExpansion<'tcx> {
    fn to_json(&self, repacker: CompilerCtxt<'_, 'tcx, BC>) -> serde_json::Value {
        json!({
            "base": self.base.to_json(repacker),
            "expansion": self.expansion.iter().map(|p| p.to_json(repacker)).collect::<Vec<_>>(),
        })
    }
}
