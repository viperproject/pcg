use tracing::instrument;

use super::borrow_pcg_edge::{BorrowPCGEdge, LocalNode, ToBorrowsEdge};
use super::borrow_pcg_expansion::BorrowPCGExpansion;
use super::borrows_state::BorrowsState;
use super::path_condition::PathConditions;
use super::region_projection_member::RegionProjectionMember;
use crate::borrows::edge::abstraction::AbstractionType;
use crate::combined_pcs::PCGNode;
use crate::free_pcs::CapabilityKind;
use crate::rustc_interface::{ast::Mutability, middle::mir::Location};
use crate::utils::display::{DebugLines, DisplayWithRepacker};
use crate::utils::json::ToJsonWithRepacker;
use crate::utils::place::maybe_old::MaybeOldPlace;
use crate::utils::{Place, PlaceRepacker, SnapshotLocation};
use crate::{RestoreCapability, Weaken};

/// An action that is applied to a `BorrowsState` during the dataflow analysis
/// of `BorrowsVisitor`, for which consumers (e.g. Prusti) may wish to perform
/// their own effect (e.g. for an unblock, applying a magic wand).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BorrowPCGAction<'tcx> {
    pub(crate) kind: BorrowPCGActionKind<'tcx>,
    debug_context: Option<String>,
}

impl<'tcx> BorrowPCGAction<'tcx> {
    pub(crate) fn debug_line_with_context(&self, repacker: PlaceRepacker<'_, 'tcx>) -> String {
        if let Some(context) = &self.debug_context {
            format!("{}: {}", context, self.debug_line(repacker))
        } else {
            self.debug_line(repacker)
        }
    }
    pub(crate) fn debug_line(&self, repacker: PlaceRepacker<'_, 'tcx>) -> String {
        match &self.kind {
            BorrowPCGActionKind::AddAbstractionEdge(abstraction, path_conditions) => {
                format!(
                    "Add Abstraction Edge: {}; path conditions: {}",
                    abstraction.to_short_string(repacker),
                    path_conditions
                )
            }
            BorrowPCGActionKind::Weaken(weaken) => weaken.debug_line(repacker),
            BorrowPCGActionKind::Restore(restore_capability) => {
                restore_capability.debug_line(repacker)
            }
            BorrowPCGActionKind::MakePlaceOld(place) => {
                format!("Make {} an old place", place.to_short_string(repacker))
            }
            BorrowPCGActionKind::SetLatest(place, location) => format!(
                "Set Latest of {} to {:?}",
                place.to_short_string(repacker),
                location
            ),
            BorrowPCGActionKind::RemoveEdge(borrow_pcgedge) => {
                format!("Remove Edge {}", borrow_pcgedge.to_short_string(repacker))
            }
            BorrowPCGActionKind::AddRegionProjectionMember(
                region_projection_member,
                path_conditions,
            ) => format!(
                "Add Region Projection Member: {}; path conditions: {}",
                region_projection_member.to_short_string(repacker),
                path_conditions
            ),
            BorrowPCGActionKind::InsertBorrowPCGExpansion(expansion, location) => format!(
                "Insert Expansion {} at {:?}",
                expansion.to_short_string(repacker),
                location
            ),
            BorrowPCGActionKind::RenamePlace { old, new } => {
                format!("Rename {:?} to {:?}", old, new)
            }
        }
    }

    pub fn kind(&self) -> &BorrowPCGActionKind<'tcx> {
        &self.kind
    }

    pub(super) fn restore_capability(node: LocalNode<'tcx>, capability: CapabilityKind) -> Self {
        BorrowPCGAction {
            kind: BorrowPCGActionKind::Restore(RestoreCapability::new(node, capability)),
            debug_context: None,
        }
    }

    pub(super) fn weaken(place: Place<'tcx>, from: CapabilityKind, to: CapabilityKind) -> Self {
        BorrowPCGAction {
            kind: BorrowPCGActionKind::Weaken(Weaken::new(place, from, to)),
            debug_context: None,
        }
    }

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
        expansion: BorrowPCGExpansion<'tcx, LocalNode<'tcx>>,
        location: Location,
        context: impl Into<String>,
    ) -> Self {
        BorrowPCGAction {
            kind: BorrowPCGActionKind::InsertBorrowPCGExpansion(expansion, location),
            debug_context: Some(context.into()),
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BorrowPCGActionKind<'tcx> {
    Weaken(Weaken<'tcx>),
    Restore(RestoreCapability<'tcx>),
    MakePlaceOld(Place<'tcx>),
    SetLatest(Place<'tcx>, Location),
    RemoveEdge(BorrowPCGEdge<'tcx>),
    AddRegionProjectionMember(RegionProjectionMember<'tcx>, PathConditions),
    InsertBorrowPCGExpansion(BorrowPCGExpansion<'tcx>, Location),
    AddAbstractionEdge(AbstractionType<'tcx>, PathConditions),
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
    #[must_use]
    pub(crate) fn apply_action(
        &mut self,
        action: BorrowPCGAction<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        let result = match action.kind {
            BorrowPCGActionKind::AddAbstractionEdge(abstraction, pc) => {
                let mut changed = false;
                for edge in abstraction.edges() {
                    for input in edge.inputs() {
                        changed |=
                            self.set_capability(input.into(), CapabilityKind::Lent, repacker);
                    }
                    for output in edge.outputs() {
                        changed |=
                            self.set_capability(output.into(), CapabilityKind::Exclusive, repacker);
                    }
                }
                changed |= self.insert(abstraction.to_borrow_pcg_edge(pc));
                changed
            }
            BorrowPCGActionKind::Restore(restore) => {
                let restore_node: PCGNode<'tcx> = restore.node().into();
                if let Some(cap) = self.get_capability(restore_node) {
                    assert!(cap < restore.capability());
                }
                if !restore_node.is_owned(repacker) {
                    if !self.set_capability(restore_node, restore.capability(), repacker) {
                        tracing::error!(
                            "Capability was already {:?} for {}",
                            restore.capability(),
                            restore_node.to_short_string(repacker)
                        );
                        for line in self.capabilities.debug_lines(repacker) {
                            tracing::error!("{}", line);
                        }
                        panic!("Capability should have been updated")
                    }
                }
                true
            }
            BorrowPCGActionKind::Weaken(weaken) => {
                let weaken_place: PCGNode<'tcx> = weaken.place().into();
                assert_eq!(self.get_capability(weaken_place), Some(weaken.from));
                assert!(self.set_capability(weaken_place, weaken.to, repacker));
                true
            }
            BorrowPCGActionKind::MakePlaceOld(place) => self.make_place_old(place, repacker),
            BorrowPCGActionKind::SetLatest(place, location) => {
                self.set_latest(place, location, repacker)
            }
            BorrowPCGActionKind::RemoveEdge(edge) => self.remove(&edge),
            BorrowPCGActionKind::AddRegionProjectionMember(member, pc) => {
                self.add_region_projection_member(member, pc, repacker)
            }
            BorrowPCGActionKind::InsertBorrowPCGExpansion(expansion, location) => {
                let updated = self.insert(
                    expansion
                        .clone()
                        .to_borrow_pcg_edge(PathConditions::new(location.block)),
                );
                if updated {
                    let base = expansion.base();
                    let expanded_capability = match &expansion {
                        BorrowPCGExpansion::FromOwned(expansion_of_owned) => {
                            match expansion_of_owned.base().ty(repacker).ty.ref_mutability() {
                                Some(Mutability::Mut) => CapabilityKind::Exclusive,
                                Some(Mutability::Not) => CapabilityKind::Read,
                                None => unreachable!(),
                            }
                        }
                        BorrowPCGExpansion::FromBorrow(expansion_of_borrowed) => {
                            if let Some(capability) =
                                self.get_capability(expansion_of_borrowed.base.into())
                            {
                                capability
                            } else {
                                // Presumably already expanded in another branch
                                // TODO: Check expansion capability exists
                                return true;
                            }
                        }
                    };

                    // If the expansion is a deref of a borrow, its expansion should not
                    // change the capability to the base. We are allowed to have e.g. exclusive
                    // permission to `x: &'a mut T` and `*x` simultaneously. Intuitively, `*x`
                    // gets its permission from `x↓'a`.
                    if !expansion.is_deref_of_borrow(repacker) {
                        match expanded_capability {
                            CapabilityKind::Read => {
                                _ = self.set_capability(
                                    base.into(),
                                    CapabilityKind::Read,
                                    repacker,
                                );
                            }
                            _ => {
                                _ = self.remove_capability(base);
                            }
                        }
                    }

                    for p in expansion.expansion(repacker).iter() {
                        _ = self.set_capability((*p).into(), expanded_capability, repacker);
                    }
                }
                updated
            }
            BorrowPCGActionKind::RenamePlace { old, new } => {
                self.change_pcs_elem(old, new, repacker)
            }
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
            changed |= self.set_capability(*i, input_cap, repacker);
        }
        for o in member.outputs.iter() {
            changed |= self.set_capability((*o).into(), output_cap, repacker);
        }
        changed
    }

    #[must_use]
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
