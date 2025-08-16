// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

pub(crate) mod join;

use std::fmt::{Debug, Formatter, Result};

use crate::{
    borrow_pcg::borrow_pcg_expansion::PlaceExpansion,
    error::PcgUnsupportedError,
    owned_pcg::{RepackCollapse, RepackGuide},
    pcg::place_capabilities::{
        PlaceCapabilities, PlaceCapabilitiesInterface, PlaceCapabilitiesReader,
    },
    rustc_interface::middle::mir::Local,
    utils::{HasCompilerCtxt, data_structures::HashSet},
};
use itertools::Itertools;

use crate::{
    error::PcgInternalError,
    owned_pcg::RepackOp,
    pcg::CapabilityKind,
    utils::{CompilerCtxt, Place, display::DisplayWithCompilerCtxt},
};

#[derive(Clone, PartialEq, Eq)]
/// The permissions of a local, each key in the hashmap is a "root" projection of the local
/// Examples of root projections are: `_1`, `*_1.f`, `*(*_.f).g` (i.e. either a local or a deref)
pub enum OwnedPcgLocal<'tcx> {
    Unallocated,
    Allocated(LocalExpansions<'tcx>),
}

impl Debug for OwnedPcgLocal<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Self::Unallocated => write!(f, "U"),
            Self::Allocated(cps) => write!(f, "{cps:?}"),
        }
    }
}

impl<'tcx> OwnedPcgLocal<'tcx> {
    pub(crate) fn check_validity(
        &self,
        capabilities: &PlaceCapabilities<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> std::result::Result<(), String> {
        match self {
            Self::Unallocated => Ok(()),
            Self::Allocated(cps) => cps.check_validity(capabilities, ctxt),
        }
    }
    pub fn get_allocated(&self) -> &LocalExpansions<'tcx> {
        match self {
            Self::Allocated(cps) => cps,
            Self::Unallocated => panic!("Expected allocated local"),
        }
    }
    pub fn get_allocated_mut(&mut self) -> &mut LocalExpansions<'tcx> {
        match self {
            Self::Allocated(cps) => cps,
            Self::Unallocated => panic!("Expected allocated local"),
        }
    }
    pub fn new(local: Local) -> Self {
        Self::Allocated(LocalExpansions::new(local))
    }
    pub fn is_unallocated(&self) -> bool {
        matches!(self, Self::Unallocated)
    }
}

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub(crate) struct ExpandedPlace<'tcx> {
    pub(crate) place: Place<'tcx>,
    pub(crate) expansion: PlaceExpansion<'tcx>,
}

impl<'tcx> ExpandedPlace<'tcx> {
    pub(crate) fn guide(&self) -> Option<RepackGuide> {
        self.expansion.guide()
    }

    pub(crate) fn expansion_places<'a>(
        &self,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> std::result::Result<HashSet<Place<'tcx>>, PcgUnsupportedError>
    where
        'tcx: 'a,
    {
        Ok(self
            .place
            .expansion_places(&self.expansion, ctxt)?
            .into_iter()
            .collect())
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct LocalExpansions<'tcx> {
    local: Local,
    pub(crate) expansions: HashSet<ExpandedPlace<'tcx>>,
}

impl<'tcx> LocalExpansions<'tcx> {
    pub(crate) fn contains_place(&self, place: Place<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        place == self.local.into() || self.contains_expansion_to(place, ctxt)
    }

    pub(crate) fn check_validity(
        &self,
        capabilities: &PlaceCapabilities<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> std::result::Result<(), String> {
        for expansion in self.expansions.iter() {
            if let Some(CapabilityKind::Write) = capabilities.get(expansion.place, ctxt) {
                return Err(format!(
                    "Base {} of expansion {:?} has write capability",
                    expansion.place.to_short_string(ctxt),
                    expansion
                ));
            }
        }
        Ok(())
    }
    pub(crate) fn has_expansions(&self) -> bool {
        !self.expansions.is_empty()
    }

    pub(crate) fn remove_all_expansions_from<'a>(
        &mut self,
        place: Place<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) where
        'tcx: 'a,
    {
        tracing::debug!(
            "Removing all expansions from {}",
            place.to_short_string(ctxt.ctxt())
        );
        self.expansions.retain(|pe| pe.place != place);
    }

    pub(crate) fn insert_expansion(&mut self, place: Place<'tcx>, expansion: PlaceExpansion<'tcx>) {
        self.expansions.insert(ExpandedPlace { place, expansion });
    }

    pub(crate) fn expansions(&self) -> &HashSet<ExpandedPlace<'tcx>> {
        &self.expansions
    }

    pub(crate) fn leaf_expansions<'a>(
        &self,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> HashSet<ExpandedPlace<'tcx>>
    where
        'tcx: 'a,
    {
        self.expansions
            .iter()
            .filter(|e| {
                e.expansion_places(ctxt)
                    .unwrap()
                    .iter()
                    .all(|p| !self.contains_expansion_from(*p))
            })
            .cloned()
            .collect()
    }

    pub(crate) fn is_leaf_place(&self, place: Place<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        self.leaf_places(ctxt).contains(&place)
    }

    pub fn leaf_places<'a>(&self, repacker: impl HasCompilerCtxt<'a, 'tcx>) -> HashSet<Place<'tcx>>
    where
        'tcx: 'a,
    {
        if self.expansions.is_empty() {
            return vec![self.local.into()].into_iter().collect();
        }
        self.expansions
            .iter()
            .flat_map(|e| e.expansion_places(repacker).unwrap())
            .filter(|p| !self.contains_expansion_from(*p))
            .collect::<HashSet<_>>()
    }

    pub fn new(local: Local) -> Self {
        Self {
            local,
            expansions: HashSet::default(),
        }
    }

    pub(crate) fn contains_expansion_from(&self, place: Place<'tcx>) -> bool {
        self.expansions.iter().any(|e| e.place == place)
    }

    pub(crate) fn expansions_from(
        &self,
        place: Place<'tcx>,
    ) -> impl Iterator<Item = &ExpandedPlace<'tcx>> {
        self.expansions.iter().filter(move |e| e.place == place)
    }

    pub(crate) fn contains_expansion_to<'a>(
        &self,
        place: Place<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> bool
    where
        'tcx: 'a,
    {
        self.expansions
            .iter()
            .any(|e| e.expansion_places(ctxt).unwrap().contains(&place))
    }

    pub(crate) fn get_local(&self) -> Local {
        self.local
    }

    pub(crate) fn places_to_collapse_for_obtain_of<'a>(
        &self,
        place: Place<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Vec<Place<'tcx>>
    where
        'tcx: 'a,
    {
        if !self.contains_expansion_from(place) {
            return vec![];
        }
        let mut places = self
            .all_descendants_of(place, ctxt)
            .difference(&self.leaf_places(ctxt))
            .sorted_by_key(|place| place.projection().len())
            .rev()
            .cloned()
            .collect::<Vec<_>>();
        places.push(place);
        places
    }

    pub(crate) fn collapse<'a, Ctxt: HasCompilerCtxt<'a, 'tcx>>(
        &mut self,
        to: Place<'tcx>,
        _for_cap: Option<CapabilityKind>,
        capabilities: &mut impl PlaceCapabilitiesInterface<'tcx>,
        ctxt: Ctxt,
    ) -> std::result::Result<Vec<RepackOp<'tcx>>, PcgInternalError>
    where
        'tcx: 'a,
    {
        if !self.contains_expansion_from(to) {
            return Ok(vec![]);
        }
        let places_to_collapse = self.places_to_collapse_for_obtain_of(to, ctxt);
        let ops: Vec<RepackOp<'tcx>> = places_to_collapse
            .into_iter()
            .map(|place| {
                let retained_cap = self
                    .get_retained_capability_of_children(place, capabilities, ctxt)
                    .unwrap();
                let action = RepackCollapse::new(place, retained_cap.expect_concrete());
                self.perform_collapse_action(action, capabilities, ctxt)
                    .unwrap();
                RepackOp::Collapse(action)
            })
            .collect();
        Ok(ops)
    }
}
