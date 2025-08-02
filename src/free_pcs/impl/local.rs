// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::fmt::{Debug, Formatter, Result};

use crate::{
    borrow_pcg::borrow_pcg_expansion::PlaceExpansion,
    free_pcs::RepackGuide,
    pcg::place_capabilities::{BlockType, PlaceCapabilities, PlaceCapabilitiesInterface},
    pcg_validity_assert,
    rustc_interface::middle::mir::Local,
    utils::data_structures::HashSet,
};
use itertools::Itertools;

use crate::{
    free_pcs::{CapabilityKind, RepackOp},
    pcg::{PcgError, PcgInternalError},
    utils::{CompilerCtxt, Place, corrected::CorrectedPlace, display::DisplayWithCompilerCtxt},
};

#[derive(Clone, PartialEq, Eq)]
/// The permissions of a local, each key in the hashmap is a "root" projection of the local
/// Examples of root projections are: `_1`, `*_1.f`, `*(*_.f).g` (i.e. either a local or a deref)
pub enum CapabilityLocal<'tcx> {
    Unallocated,
    Allocated(LocalExpansions<'tcx>),
}

impl Debug for CapabilityLocal<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Self::Unallocated => write!(f, "U"),
            Self::Allocated(cps) => write!(f, "{cps:?}"),
        }
    }
}

impl<'tcx> CapabilityLocal<'tcx> {
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
    pub(crate) fn arbitrary_expansion_place(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Place<'tcx> {
        self.expansion_places(ctxt).into_iter().next().unwrap()
    }
    pub(crate) fn expansion_places(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> HashSet<Place<'tcx>> {
        self.place
            .expansion_places(&self.expansion, ctxt)
            .into_iter()
            .collect()
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct LocalExpansions<'tcx> {
    local: Local,
    pub(crate) expansions: HashSet<ExpandedPlace<'tcx>>,
}

impl<'tcx> LocalExpansions<'tcx> {
    pub(crate) fn remove_all_expansions_from(&mut self, place: Place<'tcx>) {
        self.expansions.retain(|pe| pe.place != place);
    }

    pub(crate) fn insert_expansion(&mut self, place: Place<'tcx>, expansion: PlaceExpansion<'tcx>) {
        self.expansions.insert(ExpandedPlace { place, expansion });
    }

    pub(crate) fn expansions(&self) -> &HashSet<ExpandedPlace<'tcx>> {
        &self.expansions
    }

    pub(crate) fn leaf_expansions(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> HashSet<ExpandedPlace<'tcx>> {
        self.expansions
            .iter()
            .filter(|e| {
                e.expansion_places(ctxt)
                    .iter()
                    .all(|p| !self.contains_expansion_from(*p))
            })
            .cloned()
            .collect()
    }

    pub fn leaves(&self, repacker: CompilerCtxt<'_, 'tcx>) -> HashSet<Place<'tcx>> {
        if self.expansions.is_empty() {
            return vec![self.local.into()].into_iter().collect();
        }
        self.expansions
            .iter()
            .flat_map(|e| e.expansion_places(repacker))
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

    pub(crate) fn contains_expansion_from_with_guide(
        &self,
        place: Place<'tcx>,
        guide: Option<RepackGuide>,
    ) -> bool {
        self.expansions
            .iter()
            .any(|e| e.place == place && e.guide() == guide)
    }

    pub(crate) fn contains_expansion_to(
        &self,
        place: Place<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.expansions
            .iter()
            .any(|e| e.expansion_places(ctxt).contains(&place))
    }

    pub(crate) fn get_local(&self) -> Local {
        self.local
    }

    pub(crate) fn expand(
        &mut self,
        from: Place<'tcx>,
        to: CorrectedPlace<'tcx>,
        for_cap: CapabilityKind,
        capabilities: &mut PlaceCapabilities<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> std::result::Result<Vec<RepackOp<'tcx>>, PcgError> {
        assert!(
            to.is_owned(repacker),
            "Expanding to borrowed place {:?}",
            *to
        );

        let from_cap = if let Some(cap) = capabilities.get(from) {
            cap
        } else {
            pcg_validity_assert!(
                false,
                "No capability for {}",
                from.to_short_string(repacker)
            );
            panic!("No capability for {}", from.to_short_string(repacker));
            // For debugging, assume exclusive, we can visualize the graph to see what's going on
            // CapabilityKind::Exclusive
        };
        let expansion = from.expand(*to, repacker)?;

        for place in expansion.other_expansions() {
            capabilities.insert(
                place,
                if for_cap.is_read() { for_cap } else { from_cap },
                repacker,
            );
        }

        let mut ops = Vec::new();

        for expansion in expansion.expansions() {
            self.insert_expansion(
                expansion.base_place(),
                PlaceExpansion::from_places(expansion.expansion(), repacker),
            );

            let block_type = if for_cap.is_read() {
                BlockType::Read
            } else {
                BlockType::Other
            };
            capabilities.update_capabilities_for_block_of_place(
                expansion.base_place(),
                block_type,
                repacker,
            );
            if expansion.kind.is_deref_box() && from_cap.is_shallow_exclusive() {
                ops.push(RepackOp::DerefShallowInit(
                    expansion.base_place(),
                    expansion.target_place,
                ));
            } else {
                ops.push(RepackOp::expand(
                    expansion.base_place(),
                    expansion.guide(),
                    for_cap,
                    repacker,
                ));
            }
        }

        capabilities.insert(*to, for_cap, repacker);

        Ok(ops)
    }

    pub(crate) fn collapse(
        &mut self,
        to: Place<'tcx>,
        _for_cap: Option<CapabilityKind>,
        capabilities: &mut PlaceCapabilities<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> std::result::Result<Vec<RepackOp<'tcx>>, PcgInternalError> {
        let expansions = self
            .expansions
            .iter()
            .filter(|pe| to.is_prefix_of(pe.place))
            .sorted_by_key(|pe| pe.place.projection().len())
            .rev()
            .cloned()
            .collect::<Vec<_>>();
        let ops = expansions
            .into_iter()
            .map(|pe| {
                let expansion_places = pe.expansion_places(ctxt);
                let retained_cap =
                    expansion_places
                        .iter()
                        .fold(CapabilityKind::Exclusive, |acc, place| {
                            match capabilities.remove(*place, ctxt) {
                                Some(cap) => acc.minimum(cap).unwrap_or(CapabilityKind::Write),
                                None => acc,
                            }
                        });
                capabilities.insert(pe.place, retained_cap, ctxt);
                self.expansions.remove(&pe);
                RepackOp::collapse(pe.place, pe.expansion.guide(), retained_cap)
            })
            .collect();
        Ok(ops)
    }
}
