use tracing::instrument;

use super::borrow_pcg_edge::BorrowPcgEdge;
use super::edge::kind::BorrowPcgEdgeKind;
use super::state::BorrowsState;
use crate::free_pcs::CapabilityKind;
use crate::pcg::place_capabilities::PlaceCapabilities;
use crate::pcg::PcgError;
use crate::rustc_interface::middle::mir::Location;
use crate::utils::display::DisplayWithCompilerCtxt;
use crate::utils::json::ToJsonWithCompilerCtxt;
use crate::utils::{CompilerCtxt, HasPlace, Place, SnapshotLocation};
use crate::{pcg_validity_assert, RestoreCapability, Weaken};

pub mod actions;

/// An action that is applied to a `BorrowsState` during the dataflow analysis
/// of `BorrowsVisitor`, for which consumers (e.g. Prusti) may wish to perform
/// their own effect (e.g. for an unblock, applying a magic wand).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BorrowPCGAction<'tcx> {
    pub(crate) kind: BorrowPcgActionKind<'tcx>,
    debug_context: Option<String>,
}

impl<'tcx> BorrowPCGAction<'tcx> {
    pub(crate) fn debug_line(&self, repacker: CompilerCtxt<'_, 'tcx>) -> String {
        match &self.kind {
            BorrowPcgActionKind::AddEdge { edge, .. } => {
                format!("Add Edge: {}", edge.to_short_string(repacker))
            }
            BorrowPcgActionKind::Weaken(weaken) => weaken.debug_line(repacker),
            BorrowPcgActionKind::Restore(restore_capability) => {
                restore_capability.debug_line(repacker)
            }
            BorrowPcgActionKind::MakePlaceOld(place, reason) => {
                format!(
                    "Make {} an old place ({:?})",
                    place.to_short_string(repacker),
                    reason
                )
            }
            BorrowPcgActionKind::SetLatest(place, location) => format!(
                "Set Latest of {} to {:?}",
                place.to_short_string(repacker),
                location
            ),
            BorrowPcgActionKind::RemoveEdge(borrow_pcgedge) => {
                format!("Remove Edge {}", borrow_pcgedge.to_short_string(repacker))
            }
        }
    }

    pub fn kind(&self) -> &BorrowPcgActionKind<'tcx> {
        &self.kind
    }

    pub(crate) fn restore_capability(place: Place<'tcx>, capability: CapabilityKind) -> Self {
        BorrowPCGAction {
            kind: BorrowPcgActionKind::Restore(RestoreCapability::new(place, capability)),
            debug_context: None,
        }
    }

    pub(crate) fn weaken(
        place: Place<'tcx>,
        from: CapabilityKind,
        to: Option<CapabilityKind>,
    ) -> Self {
        BorrowPCGAction {
            kind: BorrowPcgActionKind::Weaken(Weaken::new(place, from, to)),
            debug_context: None,
        }
    }

    pub(crate) fn set_latest(
        place: Place<'tcx>,
        location: Location,
        context: impl Into<String>,
    ) -> Self {
        BorrowPCGAction {
            kind: BorrowPcgActionKind::SetLatest(place, location),
            debug_context: Some(context.into()),
        }
    }

    pub(crate) fn remove_edge(edge: BorrowPcgEdge<'tcx>, context: impl Into<String>) -> Self {
        BorrowPCGAction {
            kind: BorrowPcgActionKind::RemoveEdge(edge),
            debug_context: Some(context.into()),
        }
    }

    pub(crate) fn add_edge(edge: BorrowPcgEdge<'tcx>, for_read: bool) -> Self {
        BorrowPCGAction {
            kind: BorrowPcgActionKind::AddEdge { edge, for_read },
            debug_context: None,
        }
    }

    pub(crate) fn make_place_old(place: Place<'tcx>, reason: MakePlaceOldReason) -> Self {
        BorrowPCGAction {
            kind: BorrowPcgActionKind::MakePlaceOld(place, reason),
            debug_context: None,
        }
    }
}

impl<'tcx> From<BorrowPcgActionKind<'tcx>> for BorrowPCGAction<'tcx> {
    fn from(kind: BorrowPcgActionKind<'tcx>) -> Self {
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
pub enum BorrowPcgActionKind<'tcx> {
    Weaken(Weaken<'tcx>),
    Restore(RestoreCapability<'tcx>),
    MakePlaceOld(Place<'tcx>, MakePlaceOldReason),
    SetLatest(Place<'tcx>, Location),
    RemoveEdge(BorrowPcgEdge<'tcx>),
    AddEdge {
        edge: BorrowPcgEdge<'tcx>,
        for_read: bool,
    },
}

impl<'tcx> DisplayWithCompilerCtxt<'tcx> for BorrowPcgActionKind<'tcx> {
    fn to_short_string(&self, repacker: CompilerCtxt<'_, 'tcx>) -> String {
        match self {
            BorrowPcgActionKind::Weaken(weaken) => weaken.debug_line(repacker),
            BorrowPcgActionKind::Restore(restore_capability) => {
                restore_capability.debug_line(repacker)
            }
            BorrowPcgActionKind::MakePlaceOld(place, reason) => {
                format!(
                    "Make {} an old place ({:?})",
                    place.to_short_string(repacker),
                    reason
                )
            }
            BorrowPcgActionKind::SetLatest(place, location) => format!(
                "Set Latest of {} to {:?}",
                place.to_short_string(repacker),
                location
            ),
            BorrowPcgActionKind::RemoveEdge(borrow_pcgedge) => {
                format!("Remove Edge {}", borrow_pcgedge.to_short_string(repacker))
            }
            BorrowPcgActionKind::AddEdge { edge, for_read } => format!(
                "Add Edge: {}; for read: {}",
                edge.to_short_string(repacker),
                for_read
            ),
        }
    }
}

impl<'tcx> ToJsonWithCompilerCtxt<'tcx> for BorrowPCGAction<'tcx> {
    fn to_json(&self, repacker: CompilerCtxt<'_, 'tcx>) -> serde_json::Value {
        self.kind.to_short_string(repacker).into()
    }
}

impl<'tcx> BorrowsState<'tcx> {
    #[instrument(skip(self, ctxt, capabilities))]
    pub(crate) fn apply_action(
        &mut self,
        action: BorrowPCGAction<'tcx>,
        capabilities: &mut PlaceCapabilities<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<bool, PcgError> {
        let result = match action.kind {
            BorrowPcgActionKind::Restore(restore) => {
                let restore_place = restore.place();
                if let Some(cap) = capabilities.get(restore_place) {
                    assert!(cap < restore.capability(), "Current capability {:?} is not less than the capability to restore to {:?}", cap, restore.capability());
                }
                if !capabilities.insert(restore_place, restore.capability()) {
                    panic!("Capability should have been updated")
                }
                true
            }
            BorrowPcgActionKind::Weaken(weaken) => {
                let weaken_place = weaken.place();
                assert_eq!(capabilities.get(weaken_place), Some(weaken.from));
                match weaken.to {
                    Some(to) => assert!(capabilities.insert(weaken_place, to)),
                    None => assert!(capabilities.remove(weaken_place).is_some()),
                }
                true
            }
            BorrowPcgActionKind::MakePlaceOld(place, _) => self.make_place_old(place, ctxt),
            BorrowPcgActionKind::SetLatest(place, location) => self.set_latest(place, location),
            BorrowPcgActionKind::RemoveEdge(edge) => self.remove(&edge, capabilities, ctxt),
            BorrowPcgActionKind::AddEdge { edge, for_read } => {
                self.handle_add_edge(edge, for_read, capabilities, ctxt)?
            }
        };
        Ok(result)
    }

    #[tracing::instrument(skip(self, capabilities, ctxt))]
    fn handle_add_edge(
        &mut self,
        edge: BorrowPcgEdge<'tcx>,
        for_read: bool,
        capabilities: &mut PlaceCapabilities<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<bool, PcgError> {
        let mut changed = self.insert(edge.clone(), ctxt);
        Ok(match edge.kind {
            BorrowPcgEdgeKind::BorrowPcgExpansion(expansion) => {
                if changed {
                    let base = expansion.base;
                    let base_capability = capabilities.get(base.place().into());
                    let expanded_capability = if expansion.is_owned_expansion(ctxt) {
                        pcg_validity_assert!(
                            base_capability.is_some(),
                            "Base capability should be set for owned expansion"
                        );
                        // TODO: Don't use exclusive as default
                        base_capability.unwrap_or(CapabilityKind::Exclusive)
                        // match expansion.base.place().ty(ctxt).ty.ref_mutability() {
                        //     Some(Mutability::Mut) => CapabilityKind::Exclusive,
                        //     Some(Mutability::Not) => CapabilityKind::Read,
                        //     None => {
                        //         unreachable!(
                        //             "Expansion base ({}: {:?}) is not a ref",
                        //             expansion.base.to_short_string(ctxt),
                        //             expansion.base.place().ty(ctxt).ty
                        //         )
                        //     }
                        // }
                    } else if for_read {
                        CapabilityKind::Read
                    } else if let Some(capability) = base_capability {
                        capability
                    } else {
                        return Ok(true);
                    };

                    if for_read {
                        changed |= capabilities.insert(base.place().into(), CapabilityKind::Read);
                    } else {
                        changed |= capabilities.remove(base.place().into()).is_some();
                    }

                    for p in expansion.expansion.iter() {
                        if !p.place().is_owned(ctxt) {
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
