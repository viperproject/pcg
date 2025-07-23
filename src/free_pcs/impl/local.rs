// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::fmt::{Debug, Formatter, Result};

use crate::{
    borrow_pcg::borrow_pcg_expansion::ExpansionFields,
    pcg::place_capabilities::{BlockType, PlaceCapabilities, PlaceCapabilitiesInterface},
    pcg_validity_assert,
    rustc_interface::{data_structures::fx::FxHashMap, middle::mir::Local},
};
use itertools::Itertools;

use crate::{
    free_pcs::{CapabilityKind, RepackOp},
    pcg::{PcgError, PcgInternalError},
    utils::{corrected::CorrectedPlace, display::DisplayWithCompilerCtxt, CompilerCtxt, Place},
};

#[derive(Clone, PartialEq, Eq)]
/// The expansions of a local, each key in the hashmap is a "root" projection of the local
/// Examples of root projections are: `_1`, `*_1.f`, `*(*_.f).g` (i.e. either a local or a deref)
pub enum OwnedPcgRoot<'tcx> {
    Unallocated,
    Allocated(PlaceExpansions<'tcx>),
}

impl Debug for OwnedPcgRoot<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Self::Unallocated => write!(f, "U"),
            Self::Allocated(cps) => write!(f, "{cps:?}"),
        }
    }
}

impl<'tcx> OwnedPcgRoot<'tcx> {
    pub fn get_allocated(&self) -> &PlaceExpansions<'tcx> {
        match self {
            Self::Allocated(cps) => cps,
            Self::Unallocated => panic!("Expected allocated local"),
        }
    }
    pub fn get_allocated_mut(&mut self) -> &mut PlaceExpansions<'tcx> {
        match self {
            Self::Allocated(cps) => cps,
            Self::Unallocated => panic!("Expected allocated local"),
        }
    }
    pub fn new(local: Local) -> Self {
        Self::Allocated(PlaceExpansions::new(local))
    }
    pub fn is_unallocated(&self) -> bool {
        matches!(self, Self::Unallocated)
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct PlaceExpansions<'tcx> {
    local: Local,
    pub(crate) expansions: FxHashMap<Place<'tcx>, ExpansionFields<'tcx>>,
}

impl<'tcx> PlaceExpansions<'tcx> {
    pub(crate) fn insert_expansion(&mut self, place: Place<'tcx>, expansion: ExpansionFields<'tcx>) {
        self.expansions.insert(place, expansion);
    }

    pub(crate) fn expansions(&self) -> &FxHashMap<Place<'tcx>, ExpansionFields<'tcx>> {
        &self.expansions
    }

    pub fn leaves(&self, repacker: CompilerCtxt<'_, 'tcx>) -> Vec<Place<'tcx>> {
        if self.expansions.is_empty() {
            return vec![self.local.into()];
        }
        self.expansions
            .iter()
            .flat_map(|(p, e)| p.expansion_places(e, repacker))
            .filter(|p| !self.contains_expansion_from(*p))
            .collect::<Vec<_>>()
    }

    pub fn new(local: Local) -> Self {
        Self {
            local,
            expansions: FxHashMap::default(),
        }
    }

    pub(crate) fn contains_expansion_from(&self, place: Place<'tcx>) -> bool {
        self.expansions.contains_key(&place)
    }

    pub(crate) fn contains_expansion_to(
        &self,
        place: Place<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        match place.last_projection() {
            Some((p, _)) => {
                if let Some(expansion) = self.expansions.get(&p) {
                    p.expansion_places(expansion, repacker).contains(&place)
                } else {
                    false
                }
            }
            None => place.local == self.local,
        }
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
                ExpansionFields::from_places(expansion.expansion(), repacker),
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
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> std::result::Result<Vec<RepackOp<'tcx>>, PcgInternalError> {
        let expansions = self
            .expansions
            .iter()
            .filter(|(p, _)| to.is_prefix_of(**p))
            .map(|(p, e)| (*p, e.clone()))
            .sorted_by_key(|(p, _)| p.projection.len())
            .rev()
            .collect::<Vec<_>>();
        let ops = expansions
            .into_iter()
            .map(|(p, expansion)| {
                let expansion_places = p.expansion_places(&expansion, repacker);
                let retained_cap =
                    expansion_places
                        .iter()
                        .fold(CapabilityKind::Exclusive, |acc, place| {
                            match capabilities.remove(*place, repacker) {
                                // TODO: Actually we shouldn't need a capability
                                Some(cap) => acc.minimum(cap).unwrap_or(CapabilityKind::Write),
                                None => acc,
                            }
                        });
                capabilities.insert(p, retained_cap, repacker);
                self.expansions.remove(&p);
                RepackOp::collapse(p, expansion.guide(), retained_cap)
            })
            .collect();
        Ok(ops)
    }
}
