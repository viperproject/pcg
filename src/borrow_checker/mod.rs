//! Defines the interface for exposing borrow-checker information to the PCG.
//!
//! Also includes implementations for the Polonius and NLL borrow-checkers.

use std::collections::BTreeSet;
use std::ops::ControlFlow;

use crate::borrow_checker::r#impl::get_reserve_location;
use crate::borrow_pcg::region_projection::PcgRegion;
use crate::pcg::PCGNode;
use crate::rustc_interface::borrowck::BorrowData;
use crate::rustc_interface::borrowck::PoloniusInput;
use crate::rustc_interface::borrowck::PoloniusOutput;
use crate::rustc_interface::borrowck::RegionInferenceContext;
use crate::rustc_interface::borrowck::{
    BorrowIndex, BorrowSet, LocationTable, PlaceConflictBias, places_conflict,
};
use crate::rustc_interface::data_structures::fx::{FxIndexMap, FxIndexSet};
use crate::rustc_interface::middle::mir::{self, Location};
use crate::rustc_interface::middle::ty::RegionVid;
use crate::utils::CompilerCtxt;
use crate::utils::Place;
use crate::utils::display::DisplayWithCompilerCtxt;

pub mod r#impl;

pub(crate) trait BorrowLike<'tcx> {
    fn get_borrowed_place(&self) -> Place<'tcx>;
}

impl<'tcx> BorrowLike<'tcx> for BorrowData<'tcx> {
    fn get_borrowed_place(&self) -> Place<'tcx> {
        self.borrowed_place().into()
    }
}

trait HasPcgRegion {
    fn pcg_region(&self) -> PcgRegion;
}

impl HasPcgRegion for BorrowData<'_> {
    fn pcg_region(&self) -> PcgRegion {
        self.region().into()
    }
}

impl<'tcx, T: RustBorrowCheckerInterface<'tcx>> BorrowCheckerInterface<'tcx> for T {
    fn is_dead(&self, node: PCGNode<'tcx>, location: Location) -> bool {
        !self.is_live(node, location)
    }

    fn twophase_borrow_activations(
        &self,
        location: Location,
    ) -> std::collections::BTreeSet<Location> {
        let activation_map = self.borrow_set().activation_map();
        if let Some(borrow_idxs) = activation_map.get(&location) {
            borrow_idxs
                .iter()
                .map(|idx| get_reserve_location(&self.borrow_set()[*idx]))
                .collect()
        } else {
            std::collections::BTreeSet::new()
        }
    }

    fn borrows_blocking(
        &self,
        blocked_place: Place<'tcx>,
        location: Location,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Vec<BorrowData<'tcx>> {
        let mut borrows = vec![];
        each_borrow_involving_path(
            &mut (),
            ctxt,
            blocked_place,
            self.borrow_set(),
            |borrow_index| self.borrow_in_scope_at(borrow_index, location),
            |_this, _, borrow| {
                borrows.push(borrow.clone());
                ControlFlow::Continue(())
            },
        );
        borrows
    }

    fn region_to_borrow_index(&self, region: PcgRegion) -> Option<BorrowIndex> {
        self.location_map()
            .iter()
            .enumerate()
            .find_map(|(index, (_, data))| {
                if data.pcg_region() == region {
                    Some(index.into())
                } else {
                    None
                }
            })
    }

    fn is_directly_blocked(
        &self,
        blocked_place: Place<'tcx>,
        location: Location,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        let mut conflict = false;
        each_borrow_involving_path(
            &mut (),
            ctxt,
            blocked_place,
            self.borrow_set(),
            |borrow_index| self.borrow_in_scope_at(borrow_index, location),
            |_this, _borrow_index, borrow| {
                if borrow.get_borrowed_place() == blocked_place {
                    conflict = true;
                    ControlFlow::Break(())
                } else {
                    ControlFlow::Continue(())
                }
            },
        );
        conflict
    }

    fn blocks(
        &self,
        blocking_place: Place<'tcx>,
        blocked_place: Place<'tcx>,
        location: Location,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        let mut conflict = false;
        each_borrow_involving_path(
            &mut (),
            ctxt,
            blocked_place,
            self.borrow_set(),
            |borrow_index| self.borrow_in_scope_at(borrow_index, location),
            |_this, borrow_index, _borrow| {
                tracing::debug!(
                    "Checking if {} contains {:?} at {:?}",
                    blocking_place.to_short_string(ctxt),
                    borrow_index,
                    location
                );
                if blocking_place.regions(ctxt).iter().any(|region| {
                    let result = self.origin_contains_loan_at(*region, borrow_index, location);
                    tracing::debug!(
                        "{} contains {:?} at {:?} = {}",
                        region,
                        borrow_index,
                        location,
                        result
                    );
                    result
                }) {
                    conflict = true;
                    ControlFlow::Break(())
                } else {
                    ControlFlow::Continue(())
                }
            },
        );
        conflict
    }

    fn as_dyn(&self) -> &dyn BorrowCheckerInterface<'tcx> {
        self
    }

    fn outlives(&self, sup: PcgRegion, sub: PcgRegion, _location: Location) -> bool {
        match (sup, sub) {
            (PcgRegion::RegionVid(sup), PcgRegion::RegionVid(sub)) => {
                self.region_infer_ctxt().eval_outlives(sup, sub)
            }
            (PcgRegion::ReStatic, _) => true,
            _ => false,
        }
    }

    fn override_region_debug_string(&self, region: RegionVid) -> Option<&str> {
        self.override_region_debug_string(region)
    }

    fn polonius_output(&self) -> Option<&PoloniusOutput> {
        self.polonius_output()
    }

    fn borrow_set(&self) -> &BorrowSet<'tcx> {
        self.borrow_set()
    }

    fn input_facts(&self) -> &PoloniusInput {
        self.input_facts()
    }

    fn borrow_index_to_region(&self, borrow_index: BorrowIndex) -> RegionVid {
        self.borrow_index_to_region(borrow_index)
    }

    fn rust_borrow_checker(&self) -> Option<&dyn RustBorrowCheckerInterface<'tcx>> {
        Some(self)
    }
}

pub trait BorrowCheckerInterface<'tcx> {
    /* Main Interface Start */

    /// Answers the question: Does `node` contain borrow extents that are not
    /// in scope at `location`?
    fn is_dead(&self, node: PCGNode<'tcx>, location: Location) -> bool;

    fn is_directly_blocked(
        &self,
        blocked_place: Place<'tcx>,
        location: Location,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool;

    fn blocks(
        &self,
        blocking_place: Place<'tcx>,
        blocked_place: Place<'tcx>,
        location: Location,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool;

    /// Returns true iff `sup` is required to outlive `sub` at `location`.
    fn outlives(&self, sup: PcgRegion, sub: PcgRegion, location: Location) -> bool;

    fn borrows_blocking(
        &self,
        blocked_place: Place<'tcx>,
        location: Location,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Vec<BorrowData<'tcx>>;

    /// Returns the set of two-phase borrows that activate at `location`.
    /// Each borrow in the returned set is represented by the MIR location
    /// that it was created at.
    fn twophase_borrow_activations(&self, location: Location) -> BTreeSet<Location>;

    /* Main Interface End */

    /// Returns true iff `reg1` outlives `reg2` and `reg2` outlives `reg1`.
    fn same_region(&self, reg1: PcgRegion, reg2: PcgRegion, location: Location) -> bool {
        self.outlives(reg1, reg2, location) && self.outlives(reg2, reg1, location)
    }

    // Implementors of this trait should be dyn-safe
    fn as_dyn(&self) -> &dyn BorrowCheckerInterface<'tcx>;

    /*
     * The remaining methods are only used for debugging / visualization.
     */

    /// If this is a Rust borrow checker, return its interface.
    /// TODO: Get rid of this at some point
    fn rust_borrow_checker(&self) -> Option<&dyn RustBorrowCheckerInterface<'tcx>>;

    /// For visualization purposes, this function can be implemented to provide
    /// human-readable names for region variables.
    fn override_region_debug_string(&self, _region: RegionVid) -> Option<&str>;

    // DEBUG ONLY
    /// If the borrow checker is based on Polonius, it can define this method to
    /// expose its output facts. This is only used for debugging /
    /// visualization.
    /// TODO: Remove
    fn polonius_output(&self) -> Option<&PoloniusOutput>;

    /// Currently only used for associating borrows with their indexes for
    /// visualization purposes.
    /// TODO: Remove
    fn region_to_borrow_index(&self, region: PcgRegion) -> Option<BorrowIndex>;

    /// TODO: Remove
    fn borrow_set(&self) -> &BorrowSet<'tcx>;

    // TODO: Remove, only for visualization
    fn input_facts(&self) -> &PoloniusInput;

    // TODO: Remove, only for visualization
    fn borrow_index_to_region(&self, borrow_index: BorrowIndex) -> RegionVid;
}

/// An interface to the results of the borrow-checker analysis. The PCG queries
/// this interface as part of its analysis, for example, to identify when borrows
/// expire.
pub trait RustBorrowCheckerInterface<'tcx> {
    /// Returns true iff the node is live *before* `location`. A node is live
    /// iff:
    /// - it is a place node, and the place is live
    /// - it is a lifetime projection node, and the lifetime is live
    ///
    /// For lifetimes, we use the notion of liveness defined here in
    /// <https://rust-lang.github.io/rfcs/2094-nll.html#liveness>:
    ///
    /// > A lifetime `L` is live at a point `P` if there is some variable `p` which is
    /// > live at `P`, and `L` appears in the type of `p`
    ///
    /// However, as referenced in the above link, there are some subtleties
    /// related to places that will be dropped. Follow the link for more details.
    fn is_live(&self, node: PCGNode<'tcx>, location: Location) -> bool;

    fn borrow_set(&self) -> &BorrowSet<'tcx>;

    fn borrow_in_scope_at(&self, borrow_index: BorrowIndex, location: Location) -> bool;

    fn origin_contains_loan_at(
        &self,
        region: PcgRegion,
        loan: BorrowIndex,
        location: Location,
    ) -> bool;

    fn region_to_borrow_index(&self, region: PcgRegion) -> Option<BorrowIndex> {
        self.location_map()
            .iter()
            .enumerate()
            .find_map(|(index, (_, data))| {
                if data.pcg_region() == region {
                    Some(index.into())
                } else {
                    None
                }
            })
    }

    fn borrow_index_to_region(&self, borrow_index: BorrowIndex) -> RegionVid {
        self.borrow_set()[borrow_index].region()
    }

    fn location_map(&self) -> &FxIndexMap<Location, BorrowData<'tcx>> {
        self.borrow_set().location_map()
    }

    /// If the borrow checker is based on Polonius, it can define this method to
    /// expose its output facts. This is only used for debugging /
    /// visualization.
    fn polonius_output(&self) -> Option<&PoloniusOutput>;

    fn override_region_debug_string(&self, region: RegionVid) -> Option<&str>;

    fn borrows_blocking(
        &self,
        blocked_place: Place<'tcx>,
        location: Location,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Vec<BorrowData<'tcx>> {
        let mut borrows = vec![];
        each_borrow_involving_path(
            &mut (),
            ctxt,
            blocked_place,
            self.borrow_set(),
            |borrow_index| self.borrow_in_scope_at(borrow_index, location),
            |_this, _, borrow| {
                borrows.push(borrow.clone());
                ControlFlow::Continue(())
            },
        );
        borrows
    }

    fn loans_killed_at(&self, location: Location) -> BTreeSet<RegionVid> {
        let location_indices = [
            self.location_table().start_index(location),
            self.location_table().mid_index(location),
        ];
        self.input_facts()
            .loan_killed_at
            .iter()
            .filter(|(_, point)| location_indices.contains(point))
            .map(|(loan, _)| self.borrow_index_to_region(*loan))
            .collect()
    }

    fn input_facts(&self) -> &PoloniusInput;

    fn region_infer_ctxt(&self) -> &RegionInferenceContext<'tcx>;

    fn location_table(&self) -> &LocationTable;
}

trait BorrowSetLike<'tcx> {
    fn get_borrows_for_local(&self, local: mir::Local) -> Option<&FxIndexSet<BorrowIndex>>;
}

impl<'tcx> BorrowSetLike<'tcx> for BorrowSet<'tcx> {
    fn get_borrows_for_local(&self, local: mir::Local) -> Option<&FxIndexSet<BorrowIndex>> {
        self.local_map().get(&local)
    }
}

pub(super) fn each_borrow_involving_path<'tcx, F, I, S>(
    s: &mut S,
    ctxt: CompilerCtxt<'_, 'tcx>,
    borrowed_place: Place<'tcx>,
    borrow_set: &BorrowSet<'tcx>,
    is_candidate: I,
    mut op: F,
) where
    F: FnMut(&mut S, BorrowIndex, &BorrowData<'tcx>) -> ControlFlow<()>,
    I: Fn(BorrowIndex) -> bool,
{
    // The number of candidates can be large, but borrows for different locals cannot conflict with
    // each other, so we restrict the working set a priori.
    let Some(borrows_for_place_base) = borrow_set.get_borrows_for_local(borrowed_place.local)
    else {
        return;
    };

    // check for loan restricting path P being used. Accounts for
    // borrows of P, P.a.b, etc.
    for &i in borrows_for_place_base {
        if !is_candidate(i) {
            continue;
        }
        let borrowed = &borrow_set[i];

        if places_conflict(
            ctxt.tcx(),
            ctxt.body(),
            borrowed.get_borrowed_place().to_rust_place(ctxt),
            borrowed_place.to_rust_place(ctxt),
            PlaceConflictBias::Overlap,
        ) {
            let ctrl = op(s, i, borrowed);
            if matches!(ctrl, ControlFlow::Break(_)) {
                return;
            }
        }
    }
}
