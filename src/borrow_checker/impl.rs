extern crate polonius_engine;
use polonius_engine::Output;

use crate::borrow_checker::BorrowCheckerInterface;
use crate::borrow_pcg::region_projection::PcgRegion;
use crate::pcg::PCGNode;
use crate::rustc_interface::borrowck::{
    BorrowData, BorrowIndex, BorrowSet, Borrows, LocationTable, PoloniusInput, PoloniusOutput,
    RegionInferenceContext, RichLocation,
};
use crate::rustc_interface::data_structures::fx::FxIndexMap;
use crate::rustc_interface::dataflow::{compute_fixpoint, with_cursor_state};
use crate::rustc_interface::middle::mir::{self, Location};
use crate::rustc_interface::middle::ty;
use crate::rustc_interface::mir_dataflow::{impls::MaybeLiveLocals, ResultsCursor};
use crate::utils::maybe_remote::MaybeRemotePlace;
use crate::utils::CompilerCtxt;
#[cfg(feature = "visualization")]
use crate::visualization::bc_facts_graph::RegionPrettyPrinter;
use crate::BodyAndBorrows;
use std::cell::{RefCell, RefMut};
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

/// An interface to the results of the Polonius borrow-checker analysis.
#[derive(Clone)]
pub struct PoloniusBorrowChecker<'mir, 'tcx: 'mir> {
    in_scope_borrows: Rc<RefCell<ResultsCursor<'mir, 'tcx, Borrows<'mir, 'tcx>>>>,
    location_table: &'mir LocationTable,
    input_facts: &'mir PoloniusInput,
    pub output_facts: PoloniusOutput,
    body: &'mir mir::Body<'tcx>,
    tcx: ty::TyCtxt<'tcx>,
    region_cx: &'mir RegionInferenceContext<'tcx>,
    borrows: &'mir BorrowSet<'tcx>,
    #[cfg(feature = "visualization")]
    pub pretty_printer: RegionPrettyPrinter<'mir, 'tcx>,
}

impl<'mir, 'tcx: 'mir> PoloniusBorrowChecker<'mir, 'tcx> {
    fn ctxt(&self) -> CompilerCtxt<'_, 'tcx> {
        CompilerCtxt::new(self.body, self.tcx, self)
    }

    pub fn new<T: BodyAndBorrows<'tcx>>(tcx: ty::TyCtxt<'tcx>, body: &'mir T) -> Self {
        let location_table = body.location_table();
        let output_facts = Output::compute(
            body.input_facts(),
            polonius_engine::Algorithm::DatafrogOpt,
            true,
        );
        let region_cx = body.region_inference_context();
        let borrows = body.borrow_set();
        Self {
            in_scope_borrows: Rc::new(RefCell::new(
                compute_fixpoint(
                    Borrows::new(tcx, body.body(), region_cx, borrows),
                    tcx,
                    body.body(),
                )
                .into_results_cursor(body.body()),
            )),
            input_facts: body.input_facts(),
            location_table,
            output_facts,
            body: body.body(),
            tcx,
            region_cx,
            borrows,
            #[cfg(feature = "visualization")]
            pretty_printer: RegionPrettyPrinter::new(region_cx),
        }
    }

    pub fn origin_live_on_entry(&self, location: RichLocation) -> Option<BTreeSet<ty::RegionVid>> {
        let origins = match location {
            RichLocation::Start(location) => self
                .output_facts
                .origin_live_on_entry
                .get(&self.location_table.start_index(location))?,
            RichLocation::Mid(location) => self
                .output_facts
                .origin_live_on_entry
                .get(&self.location_table.mid_index(location))?,
        };
        Some(origins.iter().map(|r| (*r).into()).collect())
    }

    pub fn loans_live_at(&self, location: RichLocation) -> BTreeSet<ty::RegionVid> {
        let loans = match location {
            RichLocation::Start(location) => self
                .output_facts
                .loans_in_scope_at(self.location_table.start_index(location)),
            RichLocation::Mid(location) => self
                .output_facts
                .loans_in_scope_at(self.location_table.mid_index(location)),
        };
        loans
            .iter()
            .map(|r| self.borrow_index_to_region(*r))
            .collect()
    }

    pub fn origin_contains_loan_at_map(
        &self,
        location: RichLocation,
    ) -> Option<BTreeMap<ty::RegionVid, BTreeSet<BorrowIndex>>> {
        let location_table = self.location_table();
        let loans = match location {
            RichLocation::Start(location) => self
                .output_facts
                .origin_contains_loan_at
                .get(&location_table.start_index(location))?,
            RichLocation::Mid(location) => self
                .output_facts
                .origin_contains_loan_at
                .get(&location_table.mid_index(location))?,
        };
        Some(
            loans
                .iter()
                .map(|(region, indices)| ((*region).into(), indices.clone()))
                .collect(),
        )
    }
}

impl<'mir, 'tcx: 'mir> BorrowCheckerInterface<'tcx> for PoloniusBorrowChecker<'mir, 'tcx> {
    #[cfg(feature = "visualization")]
    fn override_region_debug_string(&self, region: ty::RegionVid) -> Option<&str> {
        self.pretty_printer.lookup(region).map(|s| s.as_str())
    }
    #[cfg(not(feature = "visualization"))]
    fn override_region_debug_string(&self, _region: ty::RegionVid) -> Option<&str> {
        None
    }
    fn is_live(&self, node: PCGNode<'tcx>, location: Location) -> bool {
        let regions: Vec<_> = match node {
            PCGNode::Place(place) => place.regions(self.ctxt()).into_iter().collect(),
            PCGNode::RegionProjection(region_projection) => {
                vec![region_projection.region(self.ctxt())]
            }
        };
        let live_loans = self
            .output_facts
            .loans_in_scope_at(self.location_table.start_index(location));

        let live_origins: BTreeSet<ty::RegionVid> = self
            .output_facts
            .origins_live_at(self.location_table.start_index(location))
            .iter()
            .map(|r| (*r).into())
            .collect::<BTreeSet<_>>();
        regions.iter().any(|region| match region {
            PcgRegion::RegionVid(region_vid) => live_loans.iter().any(|loan| {
                if live_origins.contains(region_vid) {
                    return true;
                }
                if self
                    .region_cx
                    .eval_outlives(*region_vid, self.borrow_index_to_region(*loan))
                {
                    return true;
                }
                false
            }),
            PcgRegion::ReErased => todo!(),
            PcgRegion::ReStatic => todo!(),
            PcgRegion::ReBound(_, _) => todo!(),
            PcgRegion::ReLateParam(_) => todo!(),
        })
    }

    fn outlives(&self, sup: PcgRegion, sub: PcgRegion) -> bool {
        outlives(self.region_cx, sup, sub)
    }

    fn twophase_borrow_activations(
        &self,
        location: Location,
    ) -> std::collections::BTreeSet<Location> {
        twophase_borrow_activations(location, self.borrows)
    }

    fn region_infer_ctxt(&self) -> &RegionInferenceContext<'tcx> {
        self.region_cx
    }

    fn location_table(&self) -> &LocationTable {
        self.location_table
    }

    fn polonius_output(&self) -> Option<&PoloniusOutput> {
        Some(&self.output_facts)
    }

    fn as_dyn(&self) -> &dyn BorrowCheckerInterface<'tcx> {
        self
    }

    fn borrow_set(&self) -> &BorrowSet<'tcx> {
        self.borrows
    }

    fn input_facts(&self) -> &PoloniusInput {
        self.input_facts
    }

    fn origin_contains_loan_at(
        &self,
        region: PcgRegion,
        loan: BorrowIndex,
        location: Location,
    ) -> bool {
        self.origin_contains_loan_at_map(RichLocation::Start(location))
            .and_then(|map| {
                map.get(&region.vid().unwrap())
                    .map(|set| set.contains(&loan))
            })
            .unwrap_or(false)
    }

    fn borrow_in_scope_at(&self, borrow_index: BorrowIndex, location: Location) -> bool {
        self.in_scope_borrows
            .borrow_mut()
            .seek_before_primary_effect(location);
        (*self.in_scope_borrows)
            .borrow()
            .get()
            .contains(borrow_index)
    }
}

/// An interface to the results of the NLL borrow-checker analysis.
#[derive(Clone)]
pub struct BorrowCheckerImpl<'mir, 'tcx: 'mir> {
    input_facts: &'mir PoloniusInput,
    live_locals: Rc<RefCell<ResultsCursor<'mir, 'tcx, MaybeLiveLocals>>>,
    in_scope_borrows: Rc<RefCell<ResultsCursor<'mir, 'tcx, Borrows<'mir, 'tcx>>>>,
    region_cx: &'mir RegionInferenceContext<'tcx>,
    borrows: &'mir BorrowSet<'tcx>,
    location_table: &'mir LocationTable,
    #[allow(unused)]
    body: &'mir mir::Body<'tcx>,
    #[allow(unused)]
    tcx: ty::TyCtxt<'tcx>,
    #[cfg(feature = "visualization")]
    pub pretty_printer: RegionPrettyPrinter<'mir, 'tcx>,
}
fn cursor_contains_local(
    cursor: RefMut<'_, ResultsCursor<'_, '_, MaybeLiveLocals>>,
    local: mir::Local,
) -> bool {
    with_cursor_state(cursor, |state| state.contains(local))
}

impl<'mir, 'tcx: 'mir> BorrowCheckerImpl<'mir, 'tcx> {
    pub fn new<T: BodyAndBorrows<'tcx>>(tcx: ty::TyCtxt<'tcx>, body: &'mir T) -> Self {
        let region_cx = body.region_inference_context();
        let borrows = body.borrow_set();
        Self {
            body: body.body(),
            tcx,
            live_locals: Rc::new(RefCell::new(
                compute_fixpoint(MaybeLiveLocals, tcx, body.body())
                    .into_results_cursor(body.body()),
            )),
            in_scope_borrows: Rc::new(RefCell::new(
                compute_fixpoint(
                    Borrows::new(tcx, body.body(), region_cx, borrows),
                    tcx,
                    body.body(),
                )
                .into_results_cursor(body.body()),
            )),
            region_cx,
            borrows,
            location_table: body.location_table(),
            input_facts: body.input_facts(),
            #[cfg(feature = "visualization")]
            pretty_printer: RegionPrettyPrinter::new(region_cx),
        }
    }

    #[allow(unused)]
    fn ctxt(&self) -> CompilerCtxt<'mir, 'tcx, &dyn BorrowCheckerInterface<'tcx>> {
        CompilerCtxt::new(self.body, self.tcx, self)
    }
}

impl BorrowCheckerImpl<'_, '_> {
    fn local_is_live_before(&self, local: mir::Local, mut location: Location) -> bool {
        // The liveness in `MaybeLiveLocals` returns the liveness *after* the end of
        // the statement at `location`. Therefore we need to decrement the statement
        // index by 1 to get the liveness at the end of the previous statement.
        // If this is the first statement of the block, we conservatively assume it's live,
        // perhaps this could be addressed in some way?
        if location.statement_index > 0 {
            location.statement_index -= 1;
        } else {
            return true;
        }

        let mut cursor = self.live_locals.as_ref().borrow_mut();
        cursor.seek_before_primary_effect(location);
        cursor_contains_local(cursor, local)
    }
}

impl BorrowCheckerImpl<'_, '_> {}

impl<'tcx> BorrowCheckerInterface<'tcx> for BorrowCheckerImpl<'_, 'tcx> {
    #[cfg(feature = "visualization")]
    fn override_region_debug_string(&self, region: ty::RegionVid) -> Option<&str> {
        self.pretty_printer.lookup(region).map(|s| s.as_str())
    }
    #[cfg(not(feature = "visualization"))]
    fn override_region_debug_string(&self, _region: ty::RegionVid) -> Option<&str> {
        None
    }
    fn input_facts(&self) -> &PoloniusInput {
        self.input_facts
    }

    fn borrow_in_scope_at(&self, borrow_index: BorrowIndex, location: Location) -> bool {
        self.in_scope_borrows
            .borrow_mut()
            .seek_before_primary_effect(location);
        let result = (*self.in_scope_borrows)
            .borrow()
            .get()
            .contains(borrow_index);
        tracing::info!(
            "borrow_in_scope_at({:?}, {:?}) = {}",
            borrow_index,
            location,
            result
        );
        result
    }

    fn outlives(&self, sup: PcgRegion, sub: PcgRegion) -> bool {
        outlives(self.region_cx, sup, sub)
    }

    fn is_live(&self, node: PCGNode<'tcx>, location: Location) -> bool {
        #[cfg(feature = "custom-rust-toolchain")]
        if let PCGNode::RegionProjection(region_projection) = node {
            let region = region_projection.region(self.ctxt());
            if !self
                .ctxt()
                .bc
                .region_infer_ctxt()
                .has_sub_region_live_at(region.vid().unwrap(), location)
            {
                return false;
            }
        }
        let local = match node {
            PCGNode::RegionProjection(rp) => {
                if let Some(local) = rp.local() {
                    local
                } else {
                    return true; // e.g. from a constant or a remote place
                }
            }
            PCGNode::Place(MaybeRemotePlace::Local(p)) => p.local(),
            _ => {
                return true;
            }
        };
        self.local_is_live_before(local, location)
    }

    fn twophase_borrow_activations(
        &self,
        location: Location,
    ) -> std::collections::BTreeSet<Location> {
        twophase_borrow_activations(location, self.borrows)
    }

    fn region_infer_ctxt(&self) -> &RegionInferenceContext<'tcx> {
        self.region_cx
    }

    fn location_table(&self) -> &LocationTable {
        self.location_table
    }

    fn polonius_output(&self) -> Option<&PoloniusOutput> {
        None
    }

    fn as_dyn(&self) -> &dyn BorrowCheckerInterface<'tcx> {
        self
    }

    fn borrow_set(&self) -> &BorrowSet<'tcx> {
        self.borrows
    }

    fn origin_contains_loan_at(
        &self,
        region: PcgRegion,
        loan: BorrowIndex,
        _location: Location,
    ) -> bool {
        self.outlives(
            PcgRegion::RegionVid(self.borrow_index_to_region(loan)),
            region,
        )
    }
}

fn outlives(region_cx: &RegionInferenceContext<'_>, sup: PcgRegion, sub: PcgRegion) -> bool {
    match (sup, sub) {
        (PcgRegion::RegionVid(sup), PcgRegion::RegionVid(sub)) => region_cx.eval_outlives(sup, sub),
        (PcgRegion::ReStatic, _) => true,
        _ => false,
    }
}

fn twophase_borrow_activations(
    location: Location,
    borrows: &BorrowSet<'_>,
) -> std::collections::BTreeSet<Location> {
    let activation_map = get_activation_map(borrows);
    if let Some(borrow_idxs) = activation_map.get(&location) {
        borrow_idxs
            .iter()
            .map(|idx| get_reserve_location(&borrows[*idx]))
            .collect()
    } else {
        std::collections::BTreeSet::new()
    }
}

#[rustversion::since(2024-12-14)]
fn get_reserve_location(borrow: &BorrowData<'_>) -> Location {
    borrow.reserve_location()
}

#[rustversion::since(2024-12-14)]
fn get_activation_map<'a>(
    borrows: &'a BorrowSet<'_>,
) -> &'a FxIndexMap<Location, Vec<BorrowIndex>> {
    borrows.activation_map()
}

#[rustversion::before(2024-12-14)]
fn get_reserve_location(borrow: &BorrowData<'_>) -> Location {
    borrow.reserve_location
}

#[rustversion::before(2024-12-14)]
fn get_activation_map<'a, 'tcx>(
    borrows: &'a BorrowSet<'tcx>,
) -> &'a FxIndexMap<Location, Vec<BorrowIndex>> {
    &borrows.activation_map
}

#[rustversion::since(2024-12-14)]
#[allow(unused)]
fn get_region(borrow: &BorrowData<'_>) -> ty::RegionVid {
    borrow.region()
}

#[rustversion::before(2024-12-14)]
fn get_region(borrow: &BorrowData<'_>) -> ty::RegionVid {
    borrow.region
}
