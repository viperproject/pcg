use std::collections::HashMap;

use itertools::Itertools;

use crate::{
    borrow_pcg::{
        borrow_pcg_expansion::BorrowPcgExpansion,
        has_pcs_elem::LabelLifetimeProjectionPredicate,
        state::{BorrowStateMutRef, BorrowsStateLike},
    },
    error::PcgError,
    pcg::{CapabilityKind, CapabilityLike, SymbolicCapability, ctxt::AnalysisCtxt},
    rustc_interface::middle::mir,
    utils::{
        CompilerCtxt, HasBorrowCheckerCtxt, HasCompilerCtxt, HasPlace, Place,
        display::{DebugLines, DisplayWithCompilerCtxt},
        validity::HasValidityCheck,
    },
};

mod private {
    use crate::pcg::SymbolicCapability;
    use crate::rustc_interface::middle::mir;

    use crate::utils::{HasCompilerCtxt, Place};

    pub trait PlaceCapabilitiesReader<'tcx, T = SymbolicCapability> {
        fn get(&self, place: Place<'tcx>, ctxt: impl HasCompilerCtxt<'_, 'tcx>) -> Option<T>;

        fn iter(&self) -> impl Iterator<Item = (Place<'tcx>, T)> + '_;

        fn capabilities_for_strict_postfixes_of<'slf>(
            &'slf self,
            place: Place<'tcx>,
        ) -> impl Iterator<Item = (Place<'tcx>, T)> + 'slf
        where
            'tcx: 'slf,
        {
            self.iter().filter_map(move |(p, c)| {
                if place.is_strict_prefix_of(p) {
                    Some((p, c))
                } else {
                    None
                }
            })
        }
    }

    pub trait PlaceCapabilitiesInterface<'tcx, C = SymbolicCapability>:
        PlaceCapabilitiesReader<'tcx, C>
    {
        fn insert<Ctxt>(
            &mut self,
            place: Place<'tcx>,
            capability: impl Into<C>,
            ctxt: Ctxt,
        ) -> bool;

        fn remove<Ctxt>(&mut self, place: Place<'tcx>, ctxt: Ctxt) -> Option<C>;

        fn retain(&mut self, predicate: impl Fn(Place<'tcx>, C) -> bool);

        fn iter_mut<'slf>(
            &'slf mut self,
        ) -> impl Iterator<Item = (&'slf Place<'tcx>, &'slf mut C)> + 'slf
        where
            C: 'slf,
            'tcx: 'slf;

        fn owned_capabilities<'a: 'slf, 'slf, Ctxt: HasCompilerCtxt<'a, 'tcx> + 'slf>(
            &'slf mut self,
            local: mir::Local,
            ctxt: Ctxt,
        ) -> impl Iterator<Item = (Place<'tcx>, &'slf mut C)> + 'slf
        where
            C: 'static,
            'tcx: 'a,
        {
            self.iter_mut().filter_map(move |(place, capability)| {
                if place.local == local && place.is_owned(ctxt) {
                    Some((*place, capability))
                } else {
                    None
                }
            })
        }

        fn remove_all_postfixes(
            &mut self,
            place: Place<'tcx>,
            _ctxt: impl HasCompilerCtxt<'_, 'tcx>,
        ) {
            self.retain(|p, _| !place.is_prefix_of(p));
        }
    }
}
pub(crate) use private::*;

impl<'tcx, T: Copy> PlaceCapabilitiesReader<'tcx, T> for PlaceCapabilities<'tcx, T> {
    fn get(&self, place: Place<'tcx>, _ctxt: impl HasCompilerCtxt<'_, 'tcx>) -> Option<T> {
        self.0.get(&place).copied()
    }

    fn iter(&self) -> impl Iterator<Item = (Place<'tcx>, T)> + '_ {
        self.0.iter().map(|(k, v)| (*k, *v))
    }
}

impl<'tcx, C: Copy> PlaceCapabilitiesInterface<'tcx, C> for PlaceCapabilities<'tcx, C> {
    fn insert<Ctxt>(&mut self, place: Place<'tcx>, capability: impl Into<C>, _ctxt: Ctxt) -> bool {
        self.0.insert(place, capability.into()).is_some()
    }

    fn remove<Ctxt>(&mut self, place: Place<'tcx>, _ctxt: Ctxt) -> Option<C> {
        self.0.remove(&place)
    }

    fn retain(&mut self, predicate: impl Fn(Place<'tcx>, C) -> bool) {
        self.0.retain(|place, cap| predicate(*place, *cap));
    }

    fn iter_mut<'slf>(
        &'slf mut self,
    ) -> impl Iterator<Item = (&'slf Place<'tcx>, &'slf mut C)> + 'slf
    where
        C: 'slf,
        'tcx: 'slf,
    {
        self.0.iter_mut()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PlaceCapabilities<'tcx, T = CapabilityKind>(pub(crate) HashMap<Place<'tcx>, T>);

impl<T> PlaceCapabilities<'_, T> {}

impl<T> Default for PlaceCapabilities<'_, T> {
    fn default() -> Self {
        Self(HashMap::default())
    }
}

pub(crate) type SymbolicPlaceCapabilities<'tcx> = PlaceCapabilities<'tcx, SymbolicCapability>;

impl<'a, 'tcx: 'a> SymbolicPlaceCapabilities<'tcx> {
    pub(crate) fn to_concrete(
        &self,
        ctxt: impl HasCompilerCtxt<'_, 'tcx>,
    ) -> PlaceCapabilities<'tcx, CapabilityKind> {
        let mut concrete = PlaceCapabilities::default();
        for (place, cap) in self.iter() {
            concrete.insert(place, cap.expect_concrete(), ctxt);
        }
        concrete
    }

    pub(crate) fn update_for_deref<Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>>(
        &mut self,
        ref_place: Place<'tcx>,
        capability: CapabilityKind,
        ctxt: Ctxt,
    ) -> Result<bool, PcgError> {
        if capability.is_read() || ref_place.is_shared_ref(ctxt.bc_ctxt()) {
            self.insert(
                ref_place,
                SymbolicCapability::Concrete(CapabilityKind::Read),
                ctxt,
            );
            self.insert(
                ref_place.project_deref(ctxt.bc_ctxt()),
                SymbolicCapability::Concrete(CapabilityKind::Read),
                ctxt,
            );
        } else {
            self.insert(
                ref_place,
                SymbolicCapability::Concrete(CapabilityKind::Write),
                ctxt,
            );
            self.insert(
                ref_place.project_deref(ctxt.bc_ctxt()),
                SymbolicCapability::Concrete(CapabilityKind::Exclusive),
                ctxt,
            );
        }
        Ok(true)
    }

    pub(crate) fn update_for_expansion<Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>>(
        &mut self,
        expansion: &BorrowPcgExpansion<'tcx>,
        block_type: BlockType,
        ctxt: Ctxt,
    ) -> Result<bool, PcgError> {
        let mut changed = false;
        // We dont change if only expanding region projections
        if expansion.base.is_place() {
            let base = expansion.base;
            let base_capability = self.get(base.place(), ctxt);
            let expanded_capability = if let Some(capability) = base_capability {
                let concrete_cap = capability.expect_concrete();
                let expanded = block_type.expansion_capability(base.place(), concrete_cap, ctxt);
                SymbolicCapability::Concrete(expanded)
            } else {
                return Ok(true);
            };

            changed |= self.update_capabilities_for_block_of_place(base.place(), block_type, ctxt);

            for p in expansion.expansion.iter() {
                changed |= self.insert(p.place(), expanded_capability, ctxt);
            }
        }
        Ok(changed)
    }

    pub(crate) fn update_capabilities_for_block_of_place<Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>>(
        &mut self,
        blocked_place: Place<'tcx>,
        block_type: BlockType,
        ctxt: Ctxt,
    ) -> bool {
        let retained_capability = block_type.blocked_place_maximum_retained_capability();
        if let Some(capability) = retained_capability {
            self.insert(
                blocked_place,
                SymbolicCapability::Concrete(capability),
                ctxt,
            )
        } else {
            self.remove(blocked_place, ctxt).is_some()
        }
    }
}

impl<'tcx> HasValidityCheck<'tcx> for PlaceCapabilities<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        for (place, cap) in self.iter() {
            if place.projects_shared_ref(ctxt) && !cap.is_read() {
                return Err(format!(
                    "Place {} projects a shared ref, but has capability {:?}",
                    place.to_short_string(ctxt),
                    cap
                ));
            }
        }
        for (local, _) in ctxt.body().local_decls.iter_enumerated() {
            let caps_from_local = self
                .iter()
                .filter(|(place, _)| place.local == local)
                .sorted_by_key(|(place, _)| place.projection.len())
                .collect_vec();
            if caps_from_local.is_empty() {
                continue;
            }
            fn allowed_child_cap<'tcx>(
                parent_place: Place<'tcx>,
                parent_cap: CapabilityKind,
                child_cap: CapabilityKind,
                ctxt: CompilerCtxt<'_, 'tcx>,
            ) -> bool {
                match (parent_cap, child_cap) {
                    (CapabilityKind::Write, _) if parent_place.ref_mutability(ctxt).is_some() => {
                        true
                    }
                    (CapabilityKind::Read, CapabilityKind::Read) => true,
                    _ => false,
                }
            }
            for i in 0..caps_from_local.len() - 1 {
                let (place, parent_cap) = caps_from_local[i];
                for (other_place, other_cap) in caps_from_local.iter().skip(i + 1) {
                    let (other_place, other_cap) = (*other_place, *other_cap);
                    if place.is_prefix_of(other_place)
                        && !allowed_child_cap(place, parent_cap, other_cap, ctxt)
                    {
                        return Err(format!(
                            "Place ({}: {}) with capability {:?} has a child {} with capability {:?} which is not allowed",
                            place.to_short_string(ctxt),
                            place.ty(ctxt).ty,
                            parent_cap,
                            other_place.to_short_string(ctxt),
                            other_cap
                        ));
                    }
                }
            }
        }
        Ok(())
    }
}

impl<'tcx> DebugLines<CompilerCtxt<'_, 'tcx>> for SymbolicPlaceCapabilities<'tcx> {
    fn debug_lines(&self, repacker: CompilerCtxt<'_, 'tcx>) -> Vec<String> {
        self.iter()
            .map(|(node, capability)| {
                format!(
                    "{}: {:?}",
                    node.to_short_string(repacker),
                    capability.expect_concrete()
                )
            })
            .sorted()
            .collect()
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum BlockType {
    /// Derefing a mutable reference, *not* in the context of a two-phase borrow
    /// of otherwise just for read. The reference will be downgraded to w.
    DerefMutRefForExclusive,
    /// Dereferencing a mutable reference that is stored under a shared borrow
    DerefMutRefUnderSharedRef,
    DerefSharedRef,
    Read,
    Other,
}

impl BlockType {
    pub(crate) fn blocked_place_maximum_retained_capability(self) -> Option<CapabilityKind> {
        match self {
            BlockType::DerefSharedRef => Some(CapabilityKind::Exclusive),
            BlockType::DerefMutRefForExclusive => Some(CapabilityKind::Write),
            BlockType::DerefMutRefUnderSharedRef => Some(CapabilityKind::Read),
            BlockType::Read => Some(CapabilityKind::Read),
            BlockType::Other => None,
        }
    }
    pub(crate) fn expansion_capability<'tcx>(
        self,
        _blocked_place: Place<'tcx>,
        blocked_capability: CapabilityKind,
        _ctxt: impl HasCompilerCtxt<'_, 'tcx>,
    ) -> CapabilityKind {
        match self {
            BlockType::DerefMutRefUnderSharedRef => CapabilityKind::Read,
            BlockType::DerefMutRefForExclusive => CapabilityKind::Exclusive,
            BlockType::Read => CapabilityKind::Read,
            BlockType::Other => blocked_capability,
            BlockType::DerefSharedRef => CapabilityKind::Read,
        }
    }
}

impl<'tcx, C: CapabilityLike> PlaceCapabilities<'tcx, C>
where
    Self: PlaceCapabilitiesInterface<'tcx, C>,
{
    pub(crate) fn regain_loaned_capability<'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>>(
        &mut self,
        place: Place<'tcx>,
        capability: C,
        mut borrows: BorrowStateMutRef<'_, 'tcx>,
        ctxt: Ctxt,
    ) -> Result<(), PcgError>
    where
        'tcx: 'a,
        C: 'static,
    {
        self.insert((*place).into(), capability, ctxt);
        if capability == CapabilityKind::Exclusive.into() {
            borrows.label_region_projection(
                &LabelLifetimeProjectionPredicate::AllFuturePostfixes(place),
                None,
                ctxt,
            );
        }
        Ok(())
    }

    pub(crate) fn remove_all_for_local(
        &mut self,
        local: mir::Local,
        _ctxt: impl HasCompilerCtxt<'_, 'tcx>,
    ) {
        self.0.retain(|place, _| place.local != local);
    }
}

impl<C: CapabilityLike> PlaceCapabilities<'_, C> {
    pub(crate) fn join<Ctxt: Copy>(&mut self, other: &Self, ctxt: Ctxt) -> bool
    where
        C: 'static,
    {
        let mut changed = false;
        self.0.retain(|place, _| other.0.contains_key(place));
        for (place, other_capability) in other.iter() {
            if let Some(self_capability) = self.0.get(&place) {
                if let Some(c) = self_capability.minimum(other_capability, ctxt) {
                    changed |= self.0.insert(place, c) != Some(c);
                } else {
                    self.0.remove(&place);
                    changed = true;
                }
            }
        }
        changed
    }
}

impl<'tcx, C: Copy + PartialEq> PlaceCapabilities<'tcx, C> {
    pub(crate) fn uniform_capability<'a>(
        &self,
        mut places: impl Iterator<Item = Place<'tcx>>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Option<C>
    where
        'tcx: 'a,
    {
        let cap = self.get(places.next()?, ctxt)?;
        for p in places {
            if self.get(p, ctxt) != Some(cap) {
                return None;
            }
        }
        Some(cap)
    }

    pub(crate) fn remove_all_strict_postfixes<'a>(
        &mut self,
        place: Place<'tcx>,
        _ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) where
        'tcx: 'a,
    {
        self.0.retain(|p, _| !place.is_strict_prefix_of(*p));
    }
}

impl<'tcx> PlaceCapabilities<'tcx> {
    pub(crate) fn retain(&mut self, predicate: impl Fn(&Place<'tcx>, &CapabilityKind) -> bool) {
        self.0.retain(|place, cap| predicate(place, cap));
    }

    pub(crate) fn update_for_deref(
        &mut self,
        ref_place: Place<'tcx>,
        capability: CapabilityKind,
        ctxt: AnalysisCtxt<'_, 'tcx>,
    ) -> Result<bool, PcgError> {
        if capability.is_read() || ref_place.is_shared_ref(ctxt.ctxt) {
            self.insert(ref_place, CapabilityKind::Read, ctxt);
            self.insert(
                ref_place.project_deref(ctxt.ctxt),
                CapabilityKind::Read,
                ctxt,
            );
        } else {
            self.insert(ref_place, CapabilityKind::Write, ctxt);
            self.insert(
                ref_place.project_deref(ctxt.ctxt),
                CapabilityKind::Exclusive,
                ctxt,
            );
        }
        Ok(true)
    }

    #[tracing::instrument(skip(self, expansion, ctxt))]
    pub(crate) fn update_for_expansion(
        &mut self,
        expansion: &BorrowPcgExpansion<'tcx>,
        block_type: BlockType,
        ctxt: AnalysisCtxt<'_, 'tcx>,
    ) -> Result<bool, PcgError> {
        let mut changed = false;
        // We dont change if only expanding region projections
        if expansion.base.is_place() {
            let base = expansion.base;
            let base_capability = self.get(base.place(), ctxt.ctxt);
            let expanded_capability = if let Some(capability) = base_capability {
                block_type.expansion_capability(base.place(), capability, ctxt.ctxt)
            } else {
                // TODO
                // pcg_validity_assert!(
                //     false,
                //     "Base capability for {} is not set",
                //     base.place().to_short_string(ctxt)
                // );
                return Ok(true);
                // panic!("Base capability should be set");
            };

            changed |= self.update_capabilities_for_block_of_place(base.place(), block_type, ctxt);

            for p in expansion.expansion.iter() {
                changed |= self.insert(p.place(), expanded_capability, ctxt);
            }
        }
        Ok(changed)
    }
    pub(crate) fn update_capabilities_for_block_of_place(
        &mut self,
        blocked_place: Place<'tcx>,
        block_type: BlockType,
        ctxt: AnalysisCtxt<'_, 'tcx>,
    ) -> bool {
        let max_retained_capability = block_type.blocked_place_maximum_retained_capability();
        if let Some(max_retained_cap) = max_retained_capability {
            let resulting_cap = self
                .get(blocked_place, ctxt.ctxt)
                .unwrap()
                .minimum(max_retained_cap)
                .unwrap();
            self.insert(blocked_place, resulting_cap, ctxt)
        } else {
            self.remove(blocked_place, ctxt).is_some()
        }
    }

    pub fn is_exclusive(&self, place: Place<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        self.get(place, ctxt)
            .map(|c| c == CapabilityKind::Exclusive)
            .unwrap_or(false)
    }
}
