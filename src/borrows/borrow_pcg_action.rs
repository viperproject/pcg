use tracing::instrument;

use crate::free_pcs::CapabilityKind;
use crate::rustc_interface::{ast::Mutability, middle::mir::Location};
use crate::utils::{Place, PlaceRepacker, SnapshotLocation};

use super::borrow_pcg_edge::{BorrowPCGEdge, LocalNode, ToBorrowsEdge};
use super::borrow_pcg_expansion::BorrowPCGExpansion;
use super::borrows_state::BorrowsState;
use super::domain::{MaybeOldPlace, ToJsonWithRepacker};
use super::path_condition::PathConditions;
use super::region_projection_member::RegionProjectionMember;

/// An action that is applied to a `BorrowsState` during the dataflow analysis
/// of `BorrowsVisitor`, for which consumers (e.g. Prusti) may wish to perform
/// their own effect (e.g. for an unblock, applying a magic wand).
///
/// N.B. For now these are only used for debugging. Currently annotations for
/// consumers are generated via the `bridge` functionality which generates
/// annotations between two arbitrary `BorrowsState`s. Perhaps we want to remove
/// that functionality and instead generate annotations for consumers directly
/// in the `BorrowsVisitor`?
#[derive(Clone, Debug)]
pub struct BorrowPCGAction<'tcx> {
    kind: BorrowPCGActionKind<'tcx>,
    debug_context: Option<String>,
}

impl<'tcx> BorrowPCGAction<'tcx> {
    pub(super) fn rename_place(old: MaybeOldPlace<'tcx>, new: MaybeOldPlace<'tcx>) -> Self {
        BorrowPCGAction {
            kind: BorrowPCGActionKind::RenamePlace { old, new },
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

    pub(super) fn add_region_projection_member(
        member: RegionProjectionMember<'tcx>,
        pc: PathConditions,
        context: impl Into<String>,
    ) -> Self {
        BorrowPCGAction {
            kind: BorrowPCGActionKind::AddRegionProjectionMember(member, pc),
            debug_context: Some(context.into()),
        }
    }

    pub(super) fn insert_borrow_pcg_expansion(
        de: BorrowPCGExpansion<'tcx, LocalNode<'tcx>>,
        location: Location,
    ) -> Self {
        BorrowPCGAction {
            kind: BorrowPCGActionKind::InsertBorrowPCGExpansion(de, location),
            debug_context: None,
        }
    }

    pub(super) fn make_place_old(place: Place<'tcx>) -> Self {
        BorrowPCGAction {
            kind: BorrowPCGActionKind::MakePlaceOld(place),
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

#[derive(Clone, Debug)]
pub(crate) enum BorrowPCGActionKind<'tcx> {
    MakePlaceOld(Place<'tcx>),
    SetLatest(Place<'tcx>, Location),
    RemoveEdge(BorrowPCGEdge<'tcx>),
    AddRegionProjectionMember(RegionProjectionMember<'tcx>, PathConditions),
    InsertBorrowPCGExpansion(BorrowPCGExpansion<'tcx, LocalNode<'tcx>>, Location),
    RenamePlace {
        old: MaybeOldPlace<'tcx>,
        new: MaybeOldPlace<'tcx>,
    },
}

impl<'tcx> ToJsonWithRepacker<'tcx> for BorrowPCGAction<'tcx> {
    fn to_json(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        if let Some(context) = &self.debug_context {
            format!("{}: {:?}", context, self.kind).into()
        } else {
            format!("{:?}", self).into()
        }
    }
}

impl<'tcx> BorrowsState<'tcx> {
    #[instrument(skip(self, repacker), fields(action))]
    pub(crate) fn apply_action(
        &mut self,
        action: BorrowPCGAction<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        let result = match action.kind {
            BorrowPCGActionKind::MakePlaceOld(place) => self.make_place_old(place, repacker, None),
            BorrowPCGActionKind::SetLatest(place, location) => {
                self.set_latest(place, location, repacker)
            }
            BorrowPCGActionKind::RemoveEdge(edge) => self.remove(&edge),
            BorrowPCGActionKind::AddRegionProjectionMember(member, pc) => {
                self.add_region_projection_member(member, pc, repacker)
            }
            BorrowPCGActionKind::InsertBorrowPCGExpansion(de, location) => {
                let inserted = self.insert(
                    de.clone()
                        .to_borrow_pcg_edge(PathConditions::new(location.block)),
                );
                if inserted {
                    let base = de.base();
                    let capability = match self.get_capability(base) {
                        Some(c) => c,
                        None => {
                            return inserted;
                        }
                    };
                    match capability {
                        CapabilityKind::Read => {
                            self.set_capability(base, CapabilityKind::Read);
                        }
                        _ => {
                            self.remove_capability(base);
                        }
                    }
                    for p in de.expansion(repacker).iter() {
                        self.set_capability(*p, capability);
                    }
                }
                inserted
            }
            BorrowPCGActionKind::RenamePlace { old, new } => self.change_pcs_elem(old, new),
        };
        result
    }

    /// Adds a region projection member to the graph and sets appropriate
    /// capabilities for the place and projection
    fn add_region_projection_member(
        &mut self,
        member: RegionProjectionMember<'tcx>,
        pc: PathConditions,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        let mut changed = self.insert(member.clone().to_borrow_pcg_edge(pc));
        let (input_cap, output_cap) = if member.mutability(repacker) == Mutability::Mut {
            (CapabilityKind::Lent, CapabilityKind::Exclusive)
        } else {
            (CapabilityKind::Read, CapabilityKind::Read)
        };
        for i in member.inputs.iter() {
            changed |= self.set_capability(*i, input_cap);
        }
        for o in member.outputs.iter() {
            changed |= self.set_capability(*o, output_cap);
        }
        changed
    }

    fn set_latest<T: Into<SnapshotLocation>>(
        &mut self,
        place: Place<'tcx>,
        location: T,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        let location = location.into();
        self.latest.insert(place, location.into(), repacker)
    }
}
