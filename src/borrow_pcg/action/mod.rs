use tracing::instrument;

use super::borrow_pcg_edge::BorrowPCGEdge;
use super::edge::kind::BorrowPCGEdgeKind;
use super::state::BorrowsState;
use crate::free_pcs::CapabilityKind;
use crate::pcg::place_capabilities::PlaceCapabilities;
use crate::pcg::PcgError;
use crate::rustc_interface::{ast::Mutability, middle::mir::Location};
use crate::utils::display::DisplayWithRepacker;
use crate::utils::json::ToJsonWithRepacker;
use crate::utils::place::maybe_old::MaybeOldPlace;
use crate::utils::{HasPlace, Place, CompilerCtxt, SnapshotLocation};
use crate::{RestoreCapability, Weaken};

pub mod actions;
pub(crate) mod executed_actions;

/// An action that is applied to a `BorrowsState` during the dataflow analysis
/// of `BorrowsVisitor`, for which consumers (e.g. Prusti) may wish to perform
/// their own effect (e.g. for an unblock, applying a magic wand).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BorrowPCGAction<'tcx> {
    pub(crate) kind: BorrowPCGActionKind<'tcx>,
    debug_context: Option<String>,
}

impl<'tcx> BorrowPCGAction<'tcx> {
    pub(crate) fn debug_line(&self, repacker: CompilerCtxt<'_, 'tcx>) -> String {
        match &self.kind {
            BorrowPCGActionKind::AddEdge { edge, .. } => {
                format!("Add Edge: {}", edge.to_short_string(repacker))
            }
            BorrowPCGActionKind::Weaken(weaken) => weaken.debug_line(repacker),
            BorrowPCGActionKind::Restore(restore_capability) => {
                restore_capability.debug_line(repacker)
            }
            BorrowPCGActionKind::MakePlaceOld(place, reason) => {
                format!(
                    "Make {} an old place ({:?})",
                    place.to_short_string(repacker),
                    reason
                )
            }
            BorrowPCGActionKind::SetLatest(place, location) => format!(
                "Set Latest of {} to {:?}",
                place.to_short_string(repacker),
                location
            ),
            BorrowPCGActionKind::RemoveEdge(borrow_pcgedge) => {
                format!("Remove Edge {}", borrow_pcgedge.to_short_string(repacker))
            }
        }
    }

    pub fn kind(&self) -> &BorrowPCGActionKind<'tcx> {
        &self.kind
    }

    pub(super) fn restore_capability(
        place: MaybeOldPlace<'tcx>,
        capability: CapabilityKind,
    ) -> Self {
        BorrowPCGAction {
            kind: BorrowPCGActionKind::Restore(RestoreCapability::new(place, capability)),
            debug_context: None,
        }
    }

    pub(super) fn weaken(
        place: Place<'tcx>,
        from: CapabilityKind,
        to: Option<CapabilityKind>,
    ) -> Self {
        BorrowPCGAction {
            kind: BorrowPCGActionKind::Weaken(Weaken::new(place, from, to)),
            debug_context: None,
        }
    }

    pub(super) fn set_latest(
        place: Place<'tcx>,
        location: Location,
        context: impl Into<String>,
    ) -> Self {
        BorrowPCGAction {
            kind: BorrowPCGActionKind::SetLatest(place, location),
            debug_context: Some(context.into()),
        }
    }

    pub(super) fn remove_edge(edge: BorrowPCGEdge<'tcx>, context: impl Into<String>) -> Self {
        BorrowPCGAction {
            kind: BorrowPCGActionKind::RemoveEdge(edge),
            debug_context: Some(context.into()),
        }
    }

    pub(super) fn add_edge(edge: BorrowPCGEdge<'tcx>, for_exclusive: bool) -> Self {
        BorrowPCGAction {
            kind: BorrowPCGActionKind::AddEdge {
                edge,
                for_exclusive,
            },
            debug_context: None,
        }
    }

    pub(super) fn make_place_old(place: Place<'tcx>, reason: MakePlaceOldReason) -> Self {
        BorrowPCGAction {
            kind: BorrowPCGActionKind::MakePlaceOld(place, reason),
            debug_context: None,
        }
    }
}

impl<'tcx> From<BorrowPCGActionKind<'tcx>> for BorrowPCGAction<'tcx> {
    fn from(kind: BorrowPCGActionKind<'tcx>) -> Self {
        BorrowPCGAction {
            kind,
            debug_context: None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MakePlaceOldReason {
    StorageDead,
    ReAssign,
    MoveOut,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BorrowPCGActionKind<'tcx> {
    Weaken(Weaken<'tcx>),
    Restore(RestoreCapability<'tcx>),
    MakePlaceOld(Place<'tcx>, MakePlaceOldReason),
    SetLatest(Place<'tcx>, Location),
    RemoveEdge(BorrowPCGEdge<'tcx>),
    AddEdge {
        edge: BorrowPCGEdge<'tcx>,
        for_exclusive: bool,
    },
}

impl<'tcx> DisplayWithRepacker<'tcx> for BorrowPCGActionKind<'tcx> {
    fn to_short_string(&self, repacker: CompilerCtxt<'_, 'tcx>) -> String {
        match self {
            BorrowPCGActionKind::Weaken(weaken) => weaken.debug_line(repacker),
            BorrowPCGActionKind::Restore(restore_capability) => {
                restore_capability.debug_line(repacker)
            }
            BorrowPCGActionKind::MakePlaceOld(place, reason) => {
                format!(
                    "Make {} an old place ({:?})",
                    place.to_short_string(repacker),
                    reason
                )
            }
            BorrowPCGActionKind::SetLatest(place, location) => format!(
                "Set Latest of {} to {:?}",
                place.to_short_string(repacker),
                location
            ),
            BorrowPCGActionKind::RemoveEdge(borrow_pcgedge) => {
                format!("Remove Edge {}", borrow_pcgedge.to_short_string(repacker))
            }
            BorrowPCGActionKind::AddEdge {
                edge,
                for_exclusive,
            } => format!(
                "Add Edge: {}; for exclusive: {}",
                edge.to_short_string(repacker),
                for_exclusive
            ),
        }
    }
}

impl<'tcx> ToJsonWithRepacker<'tcx> for BorrowPCGAction<'tcx> {
    fn to_json(&self, repacker: CompilerCtxt<'_, 'tcx>) -> serde_json::Value {
        self.kind.to_short_string(repacker).into()
    }
}

impl<'tcx> BorrowsState<'tcx> {
    #[instrument(skip(self, repacker), fields(action))]
    pub(crate) fn apply_action(
        &mut self,
        action: BorrowPCGAction<'tcx>,
        capabilities: &mut PlaceCapabilities<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> Result<bool, PcgError> {
        let result = match action.kind {
            BorrowPCGActionKind::Restore(restore) => {
                let restore_place: MaybeOldPlace<'tcx> = restore.place();
                if let Some(cap) = capabilities.get(restore_place) {
                    assert!(cap < restore.capability(), "Current capability {:?} is not less than the capability to restore to {:?}", cap, restore.capability());
                }
                if !restore_place.is_owned(repacker)
                    && !capabilities.insert(restore_place, restore.capability())
                {
                    panic!("Capability should have been updated")
                }
                true
            }
            BorrowPCGActionKind::Weaken(weaken) => {
                let weaken_place: MaybeOldPlace<'tcx> = weaken.place().into();
                assert_eq!(capabilities.get(weaken_place), Some(weaken.from));
                match weaken.to {
                    Some(to) => assert!(capabilities.insert(weaken_place, to)),
                    None => assert!(capabilities.remove(weaken_place).is_some()),
                }
                true
            }
            BorrowPCGActionKind::MakePlaceOld(place, _) => self.make_place_old(place, repacker),
            BorrowPCGActionKind::SetLatest(place, location) => self.set_latest(place, location),
            BorrowPCGActionKind::RemoveEdge(edge) => self.remove(&edge, capabilities, repacker),
            BorrowPCGActionKind::AddEdge {
                edge,
                for_exclusive,
            } => self.handle_add_edge(edge, for_exclusive, capabilities, repacker)?,
        };
        Ok(result)
    }

    fn handle_add_edge(
        &mut self,
        edge: BorrowPCGEdge<'tcx>,
        for_exclusive: bool,
        capabilities: &mut PlaceCapabilities<'tcx>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> Result<bool, PcgError> {
        let mut changed = self.insert(edge.clone());
        Ok(match edge.kind {
            BorrowPCGEdgeKind::BorrowPCGExpansion(expansion) => {
                if changed {
                    let base = expansion.base;
                    let expanded_capability = if expansion.is_owned_expansion(repacker) {
                        match expansion.base.place().ty(repacker).ty.ref_mutability() {
                            Some(Mutability::Mut) => CapabilityKind::Exclusive,
                            Some(Mutability::Not) => CapabilityKind::Read,
                            None => unreachable!(),
                        }
                    } else if !for_exclusive {
                        CapabilityKind::Read
                    } else if let Some(capability) = capabilities.get(base.place().into()) {
                        capability
                    } else {
                        return Ok(true);
                    };

                    if !base.place().is_owned(repacker) {
                        if for_exclusive {
                            changed |= capabilities.remove(base.place().into()).is_some();
                        } else {
                            changed |=
                                capabilities.insert(base.place().into(), CapabilityKind::Read);
                        }
                    }

                    for p in expansion.expansion.iter() {
                        if !p.place().is_owned(repacker) {
                            changed |= capabilities.insert(p.place().into(), expanded_capability);
                        }
                    }
                }
                changed
            }
            _ => changed,
        })
    }

    #[must_use]
    fn set_latest<T: Into<SnapshotLocation>>(&mut self, place: Place<'tcx>, location: T) -> bool {
        let location = location.into();
        self.latest.insert(place, location)
    }
}
