//! Defines the interface for exposing borrow-checker information to the PCG.
//!
//! Also includes implementations for the Polonius and NLL borrow-checkers.

use std::collections::BTreeSet;

use crate::borrow_pcg::region_projection::PcgRegion;
use crate::pcg::PCGNode;
use crate::rustc_interface::middle::mir::Location;
use crate::rustc_interface::middle::ty::RegionVid;
use crate::rustc_interface::borrowck::{BorrowIndex, BorrowSet, LocationTable};
use crate::rustc_interface::borrowck::PoloniusInput;
use crate::rustc_interface::borrowck::PoloniusOutput;
use crate::rustc_interface::borrowck::RegionInferenceContext;
use crate::rustc_interface::borrowck::BorrowData;
use crate::rustc_interface::data_structures::fx::FxIndexMap;

pub mod r#impl;

/// An interface to the results of the borrow-checker analysis. The PCG queries
/// this interface as part of its analysis, for example, to identify when borrows
/// expire.
pub trait BorrowCheckerInterface<'tcx> {
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

    /// A node is dead iff it is not live. See [`BorrowCheckerInterface::is_live`]
    fn is_dead(&self, node: PCGNode<'tcx>, location: Location) -> bool {
        !self.is_live(node, location)
    }

    /// Returns true iff `sup` outlives `sub`.
    fn outlives(&self, sup: PcgRegion, sub: PcgRegion) -> bool;

    /// Returns true iff `reg1` outlives `reg2` and `reg2` outlives `reg1`.
    fn same_region(&self, reg1: PcgRegion, reg2: PcgRegion) -> bool {
        self.outlives(reg1, reg2) && self.outlives(reg2, reg1)
    }

    fn borrow_set(&self) -> &BorrowSet<'tcx>;

    #[rustversion::since(2024-12-14)]
    fn borrow_index_to_region(&self, borrow_index: BorrowIndex) -> RegionVid {
        self.borrow_set()[borrow_index].region()
    }

    #[rustversion::before(2024-12-14)]
    fn borrow_index_to_region(&self, borrow_index: BorrowIndex) -> RegionVid {
        self.borrow_set()[borrow_index].region
    }

    #[rustversion::since(2024-12-14)]
    fn location_map(&self) -> &FxIndexMap<Location, BorrowData<'tcx>> {
        self.borrow_set().location_map()
    }

    #[rustversion::before(2024-12-14)]
    fn location_map(&self) -> &FxIndexMap<Location, BorrowData<'tcx>> {
        &self.borrow_set().location_map
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

    /// For visualization purposes, this function can be implemented to provide
    /// human-readable names for region variables.
    fn override_region_debug_string(&self, _region: RegionVid) -> Option<&str>;

    fn input_facts(&self) -> &PoloniusInput;

    /// Returns the set of two-phase borrows that activate at `location`.
    /// Each borrow in the returned set is represented by the MIR location
    /// that it was created at.
    fn twophase_borrow_activations(&self, location: Location) -> BTreeSet<Location>;

    fn region_infer_ctxt(&self) -> &RegionInferenceContext<'tcx>;

    fn location_table(&self) -> &LocationTable;

    /// If the borrow checker is based on Polonius, it can define this method to
    /// expose its output facts. This is only used for debugging /
    /// visualization.
    fn polonius_output(&self) -> Option<&PoloniusOutput>;

    fn as_dyn(&self) -> &dyn BorrowCheckerInterface<'tcx>;
}
