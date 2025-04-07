extern crate polonius_engine;
use polonius_engine::Output;

use crate::borrow_pcg::coupling_graph_constructor::BorrowCheckerInterface;
use crate::borrow_pcg::region_projection::PcgRegion;
use crate::pcg::PCGNode;
use crate::rustc_interface::borrowck::{
    BorrowData, BorrowIndex, BorrowSet, LocationTable, PoloniusOutput, RegionInferenceContext,
};
use crate::rustc_interface::data_structures::fx::FxIndexMap;
use crate::rustc_interface::dataflow::compute_fixpoint;
use crate::rustc_interface::middle::mir::{self, Location};
use crate::rustc_interface::middle::ty;
use crate::rustc_interface::mir_dataflow::{impls::MaybeLiveLocals, ResultsCursor};
use crate::utils::maybe_remote::MaybeRemotePlace;
use crate::utils::{CompilerCtxt, HasPlace};
use crate::BodyAndBorrows;
use std::cell::{RefCell, RefMut};
use std::rc::Rc;

#[derive(Clone)]
pub struct PoloniusBorrowChecker<'mir, 'tcx: 'mir> {
    location_table: &'mir LocationTable,
    pub output_facts: Rc<PoloniusOutput>,
    body: &'mir mir::Body<'tcx>,
    tcx: ty::TyCtxt<'tcx>,
    region_cx: &'mir RegionInferenceContext<'tcx>,
    borrows: &'mir BorrowSet<'tcx>,
}

impl<'mir, 'tcx: 'mir> PoloniusBorrowChecker<'mir, 'tcx> {
    fn ctxt(&self) -> CompilerCtxt<'_, 'tcx, '_> {
        CompilerCtxt::new(self.body, self.tcx, self)
    }
    pub fn new<T: BodyAndBorrows<'tcx>>(tcx: ty::TyCtxt<'tcx>, body: &'mir T) -> Self {
        let location_table = body.location_table();
        let output_facts = Rc::new(Output::compute(
            body.input_facts(),
            polonius_engine::Algorithm::DatafrogOpt,
            true,
        ));
        let region_cx = body.region_inference_context();
        let borrows = body.borrow_set();
        Self {
            location_table,
            output_facts,
            body: body.body(),
            tcx,
            region_cx,
            borrows,
        }
    }
}

impl<'mir, 'tcx: 'mir> BorrowCheckerInterface<'mir, 'tcx> for PoloniusBorrowChecker<'mir, 'tcx> {
    fn is_live(&self, node: PCGNode<'tcx>, location: Location) -> bool {
        let regions: Vec<_> = match node {
            PCGNode::Place(place) => place.regions(self.ctxt()).into_iter().collect(),
            PCGNode::RegionProjection(region_projection) => {
                if let Some(place) = region_projection.base().as_local_place() {
                    let mut regions: Vec<_> =
                        place.place().regions(self.ctxt()).into_iter().collect();
                    regions.push(region_projection.region(self.ctxt()));
                    regions
                } else {
                    todo!()
                }
            }
        };
        regions.iter().any(|region| match region {
            PcgRegion::RegionVid(region_vid) => self
                .output_facts
                .origin_contains_loan_at(self.location_table.start_index(location))
                .contains_key(&(*region_vid).into()),
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

    fn as_dyn(&self) -> &dyn BorrowCheckerInterface<'mir, 'tcx> {
        self
    }
}

#[derive(Clone)]
pub struct BorrowCheckerImpl<'mir, 'tcx: 'mir> {
    cursor: Rc<RefCell<ResultsCursor<'mir, 'tcx, MaybeLiveLocals>>>,
    region_cx: &'mir RegionInferenceContext<'tcx>,
    borrows: &'mir BorrowSet<'tcx>,
    location_table: &'mir LocationTable,
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
            cursor: Rc::new(RefCell::new(
                compute_fixpoint(MaybeLiveLocals, tcx, body.body())
                    .into_results_cursor(body.body()),
            )),
            region_cx,
            borrows,
            location_table: body.location_table(),
        }
    }
}

impl<'mir, 'tcx> BorrowCheckerInterface<'mir, 'tcx> for BorrowCheckerImpl<'mir, 'tcx> {

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
        cursor_contains_local(cursor, local)
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

    fn as_dyn(&self) -> &dyn BorrowCheckerInterface<'mir, 'tcx> {
        self
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
