extern crate polonius_engine;
use polonius_engine::Output;

use crate::borrow_pcg::coupling_graph_constructor::BorrowCheckerInterface;
use crate::borrow_pcg::region_projection::PcgRegion;
use crate::pcg::PCGNode;
use crate::rustc_interface::borrowck::{
    calculate_borrows_out_of_scope_at_location, BorrowData, BorrowIndex, BorrowSet, LocationTable,
    PoloniusInput, PoloniusOutput, RegionInferenceContext, RichLocation,
};
use crate::rustc_interface::data_structures::fx::FxIndexMap;
use crate::rustc_interface::dataflow::compute_fixpoint;
use crate::rustc_interface::middle::mir::{self, Location};
use crate::rustc_interface::middle::ty;
use crate::rustc_interface::mir_dataflow::{impls::MaybeLiveLocals, ResultsCursor};
use crate::utils::maybe_remote::MaybeRemotePlace;
use crate::utils::CompilerCtxt;
use crate::visualization::bc_facts_graph::RegionPrettyPrinter;
use crate::BodyAndBorrows;
use std::cell::{RefCell, RefMut};
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

#[derive(Clone)]
pub struct PoloniusBorrowChecker<'mir, 'tcx: 'mir> {
    location_table: &'mir LocationTable,
    input_facts: &'mir PoloniusInput,
    pub output_facts: PoloniusOutput,
    body: &'mir mir::Body<'tcx>,
    tcx: ty::TyCtxt<'tcx>,
    region_cx: &'mir RegionInferenceContext<'tcx>,
    borrows: &'mir BorrowSet<'tcx>,
    pretty_printer: RegionPrettyPrinter,
}

impl<'mir, 'tcx: 'mir> PoloniusBorrowChecker<'mir, 'tcx> {
    fn ctxt(&self) -> CompilerCtxt<'_, 'tcx> {
        CompilerCtxt::new(self.body, self.tcx, self)
    }
    pub fn new<T: BodyAndBorrows<'tcx>>(
        tcx: ty::TyCtxt<'tcx>,
        body: &'mir T,
        debug_region_name_overrides: BTreeMap<ty::RegionVid, String>,
    ) -> Self {
        let location_table = body.location_table();
        let output_facts = Output::compute(
            body.input_facts(),
            polonius_engine::Algorithm::DatafrogOpt,
            true,
        );
        let region_cx = body.region_inference_context();
        let borrows = body.borrow_set();
        let mut pretty_printer = RegionPrettyPrinter::new(region_cx);
        for (region, name) in debug_region_name_overrides {
            pretty_printer.insert(region, name);
        }
        Self {
            input_facts: body.input_facts(),
            location_table,
            output_facts,
            body: body.body(),
            tcx,
            region_cx,
            borrows,
            pretty_printer,
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

    pub fn origin_contains_loan_at(
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
    fn override_region_debug_string(&self, region: ty::RegionVid) -> Option<&str> {
        self.pretty_printer.lookup(region).map(|s| s.as_str())
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

    fn region_inference_ctxt(&self) -> &RegionInferenceContext<'tcx> {
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
}

#[derive(Clone)]
pub struct BorrowCheckerImpl<'mir, 'tcx: 'mir> {
    input_facts: &'mir PoloniusInput,
    cursor: Rc<RefCell<ResultsCursor<'mir, 'tcx, MaybeLiveLocals>>>,
    out_of_scope_borrows: FxIndexMap<Location, Vec<BorrowIndex>>,
    region_cx: &'mir RegionInferenceContext<'tcx>,
    borrows: &'mir BorrowSet<'tcx>,
    location_table: &'mir LocationTable,
    body: &'mir mir::Body<'tcx>,
    tcx: ty::TyCtxt<'tcx>,
}
#[rustversion::before(2024-12-14)]
fn cursor_contains_local(
    cursor: RefMut<'_, ResultsCursor<'_, '_, MaybeLiveLocals>>,
    local: mir::Local,
) -> bool {
    cursor.contains(local)
}

#[rustversion::since(2024-12-14)]
fn cursor_contains_local(
    cursor: RefMut<'_, ResultsCursor<'_, '_, MaybeLiveLocals>>,
    local: mir::Local,
) -> bool {
    cursor.get().contains(local)
}

impl<'mir, 'tcx: 'mir> BorrowCheckerImpl<'mir, 'tcx> {
    pub fn new<T: BodyAndBorrows<'tcx>>(tcx: ty::TyCtxt<'tcx>, body: &'mir T) -> Self {
        let region_cx = body.region_inference_context();
        let borrows = body.borrow_set();
        Self {
            body: body.body(),
            tcx,
            cursor: Rc::new(RefCell::new(
                compute_fixpoint(MaybeLiveLocals, tcx, body.body())
                    .into_results_cursor(body.body()),
            )),
            region_cx,
            borrows,
            location_table: body.location_table(),
            input_facts: body.input_facts(),
            out_of_scope_borrows: calculate_borrows_out_of_scope_at_location(
                body.body(),
                region_cx,
                borrows,
            ),
        }
    }

    fn ctxt(&self) -> CompilerCtxt<'mir, 'tcx, ()> {
        CompilerCtxt::new(self.body, self.tcx, ())
    }
}

impl<'mir, 'tcx> BorrowCheckerInterface<'tcx> for BorrowCheckerImpl<'mir, 'tcx> {
    fn input_facts(&self) -> &PoloniusInput {
        self.input_facts
    }

    fn outlives(&self, sup: PcgRegion, sub: PcgRegion) -> bool {
        outlives(self.region_cx, sup, sub)
    }

    fn is_live(&self, node: PCGNode<'tcx>, mut location: Location) -> bool {
        // The liveness in `MaybeLiveLocals` returns the liveness *after* the end of
        // the statement at `location`. Therefore we need to decrement the statement
        // index by 1 to get the liveness at the end of the previous statement.
        // If this is the first statement of the block, we just say it's live,
        // perhaps this could be addressed in some way?
        if location.statement_index > 0 {
            location.statement_index -= 1;
        } else {
            return true;
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
        let mut cursor = self.cursor.as_ref().borrow_mut();
        cursor.seek_before_primary_effect(location);
        if cursor_contains_local(cursor, local) {
            return true;
        }
        if let PCGNode::RegionProjection(region_projection) = node {
            let out_of_scope_borrows = self
                .out_of_scope_borrows
                .get(&location)
                .cloned()
                .unwrap_or_default();
            let out_of_scope_borrow_regions = out_of_scope_borrows
                .iter()
                .map(|idx| self.borrow_index_to_region(*idx))
                .collect::<BTreeSet<_>>();
            let in_scope_borrows = self
                .location_map()
                .values()
                .filter(|borrow| !out_of_scope_borrow_regions.contains(&get_region(borrow)))
                .collect::<Vec<_>>();
            let region = region_projection.region(self.ctxt());
            for borrow in in_scope_borrows {
                if self.outlives(region, get_region(borrow).into()) {
                    return true;
                }
            }
        }
        false
    }

    fn twophase_borrow_activations(
        &self,
        location: Location,
    ) -> std::collections::BTreeSet<Location> {
        twophase_borrow_activations(location, self.borrows)
    }

    fn region_inference_ctxt(&self) -> &RegionInferenceContext<'tcx> {
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

    fn override_region_debug_string(&self, _region: ty::RegionVid) -> Option<&str> {
        None
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
fn get_region(borrow: &BorrowData<'_>) -> ty::RegionVid {
    borrow.region()
}

#[rustversion::before(2024-12-14)]
fn get_region(borrow: &BorrowData<'_>) -> ty::RegionVid {
    borrow.region
}
