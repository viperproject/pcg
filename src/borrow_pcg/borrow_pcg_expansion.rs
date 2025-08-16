//! Definition of expansion edges in the Borrow PCG.
use std::{collections::BTreeMap, hash::Hash, marker::PhantomData};

use derive_more::From;
use itertools::Itertools;
use serde_json::json;

use super::{
    borrow_pcg_edge::{BlockedNode, BlockingNode, LocalNode},
    edge_data::EdgeData,
    has_pcs_elem::LabelLifetimeProjection,
    region_projection::LifetimeProjectionLabel,
};
use crate::error::PcgUnsupportedError;
use crate::utils::place::corrected::CorrectedPlace;
use crate::{
    borrow_checker::BorrowCheckerInterface,
    borrow_pcg::{
        edge_data::{LabelEdgePlaces, LabelPlacePredicate},
        has_pcs_elem::{
            LabelLifetimeProjectionPredicate, LabelLifetimeProjectionResult, LabelNodeContext,
            LabelPlaceWithContext, PlaceLabeller,
        },
    },
    error::PcgError,
    r#loop::PlaceUsageType,
    owned_pcg::RepackGuide,
    pcg::{
        CapabilityKind, MaybeHasLocation, SymbolicCapability,
        obtain::ObtainType,
        place_capabilities::{BlockType, PlaceCapabilitiesReader},
    },
    pcg_validity_assert,
    utils::{HasBorrowCheckerCtxt, HasCompilerCtxt, json::ToJsonWithCompilerCtxt},
};
use crate::{
    pcg::{PCGNodeLike, PcgNode},
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
    pub(crate) fn block_type<'a>(
        &self,
        base_place: Place<'tcx>,
        obtain_type: ObtainType,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> BlockType
    where
        'tcx: 'a,
    {
        if matches!(
            obtain_type,
            ObtainType::Capability(CapabilityKind::Read)
                | ObtainType::TwoPhaseExpand
                | ObtainType::LoopInvariant {
                    usage_type: PlaceUsageType::Read,
                    ..
                }
        ) {
            BlockType::Read
        } else if matches!(self, PlaceExpansion::Deref) {
            if base_place.is_shared_ref(ctxt) {
                BlockType::DerefSharedRef
            } else if base_place.is_mut_ref(ctxt) {
                if base_place.projects_shared_ref(ctxt) {
                    BlockType::DerefMutRefUnderSharedRef
                } else {
                    BlockType::DerefMutRefForExclusive
                }
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

    pub(crate) fn from_places<'a>(
        places: Vec<Place<'tcx>>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Self
    where
        'tcx: 'a,
    {
        let mut fields = BTreeMap::new();

        for place in places {
            let corrected_place = CorrectedPlace::new(place, ctxt);
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
            PlaceExpansion::Guided(RepackGuide::ConstantIndex(c)) => {
                let mut elems = vec![(*c).into()];
                elems.extend(c.other_elems());
                elems
            }
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
        self.base.to_pcg_node(repacker) == node
    }

    fn blocked_nodes<'slf, BC: Copy>(
        &self,
        _ctxt: CompilerCtxt<'_, 'tcx, BC>,
    ) -> Box<dyn std::iter::Iterator<Item = PcgNode<'tcx>> + 'slf>
    where
        'tcx: 'slf,
    {
        Box::new(std::iter::once(self.base.into()))
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
            expansion: expansion
                .expansion
                .into_iter()
                .map(|p| p.try_into())
                .collect::<Result<Vec<_>, _>>()?,
            _marker: PhantomData,
        })
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

    /// Returns true iff the expansion is packable, i.e. without losing any
    /// information. This is the case when the expansion node labels (for
    /// places, and for region projections) are the same as the base node
    /// labels.
    pub(crate) fn is_packable(
        &self,
        capabilities: &impl PlaceCapabilitiesReader<'tcx, SymbolicCapability>,
        ctxt: impl HasCompilerCtxt<'_, 'tcx>,
    ) -> bool {
        match self.base {
            PcgNode::Place(base_place) => {
                let mut fst_cap = None;
                self.expansion.iter().all(|p| {
                    if let PcgNode::Place(MaybeLabelledPlace::Current(place)) = p {
                        if let Some(cap) = fst_cap {
                            if cap != capabilities.get(*place, ctxt) {
                                return false;
                            }
                        } else {
                            fst_cap = Some(capabilities.get(*place, ctxt));
                        }
                    }
                    base_place.place().is_prefix_exact(p.place())
                        && p.location() == base_place.location()
                })
            }
            PcgNode::LifetimeProjection(_) => false,
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

    pub(crate) fn new<'a>(
        base: P,
        expansion: PlaceExpansion<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Result<Self, PcgError>
    where
        'tcx: 'a,
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
        pcg_validity_assert!(
            !(base.is_place() && base.place().is_ref(ctxt) && expansion == PlaceExpansion::Deref),
            [ctxt],
            "Deref expansion of {} should be a Deref edge, not an expansion",
            base.place().to_short_string(ctxt.ctxt())
        );
        let result = Self {
            base,
            expansion: expansion
                .elems()
                .into_iter()
                .map(|elem| base.project_deeper(elem, ctxt.ctxt()))
                .collect::<Result<Vec<_>, _>>()?,
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
