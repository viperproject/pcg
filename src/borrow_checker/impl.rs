extern crate polonius_engine;
use polonius_engine::Output;

use crate::BodyAndBorrows;
use crate::borrow_checker::RustBorrowCheckerInterface;
use crate::borrow_pcg::region_projection::PcgRegion;
use crate::pcg::PcgNode;
use crate::rustc_interface::borrowck::{
    BorrowData, BorrowIndex, BorrowSet, Borrows, LocationTable, PoloniusInput, PoloniusOutput,
    RegionInferenceContext, RichLocation,
};
use crate::rustc_interface::dataflow::compute_fixpoint;
use crate::rustc_interface::index::bit_set::BitSet;
use crate::rustc_interface::middle::mir::{self, Location, RETURN_PLACE};
use crate::rustc_interface::middle::ty;
use crate::rustc_interface::mir_dataflow::ResultsCursor;
use crate::utils::CompilerCtxt;
use crate::utils::liveness::PlaceLiveness;
#[cfg(feature = "visualization")]
use crate::visualization::bc_facts_graph::RegionPrettyPrinter;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

#[derive(Clone)]
pub(crate) struct RustBorrowCheckerData<'mir, 'tcx: 'mir> {
    input_facts: &'mir PoloniusInput,
    in_scope_borrows: Rc<RefCell<ResultsCursor<'mir, 'tcx, Borrows<'mir, 'tcx>>>>,
    location_table: &'mir LocationTable,
    body: &'mir mir::Body<'tcx>,
    tcx: ty::TyCtxt<'tcx>,
    pub(crate) borrows: &'mir BorrowSet<'tcx>,
    pub(crate) region_cx: &'mir RegionInferenceContext<'tcx>,
    #[cfg(feature = "visualization")]
    pub(crate) pretty_printer: RegionPrettyPrinter<'mir, 'tcx>,
}

impl<'mir, 'tcx: 'mir> RustBorrowCheckerData<'mir, 'tcx> {
    pub(crate) fn borrows_in_scope_at(
        &self,
        location: Location,
        before: bool,
    ) -> BitSet<BorrowIndex> {
        if before {
            self.in_scope_borrows
                .borrow_mut()
                .seek_before_primary_effect(location);
        } else {
            self.in_scope_borrows
                .borrow_mut()
                .seek_after_primary_effect(location);
        }
        self.in_scope_borrows.borrow().get().clone()
    }
    pub(crate) fn new<T: BodyAndBorrows<'tcx>>(tcx: ty::TyCtxt<'tcx>, body: &'mir T) -> Self {
        let location_table = body.location_table();
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
            body: body.body(),
            tcx,
            region_cx,
            borrows,
            #[cfg(feature = "visualization")]
            pretty_printer: RegionPrettyPrinter::new(region_cx),
        }
    }
}

/// An interface to the results of the Polonius borrow-checker analysis.
#[derive(Clone)]
pub struct PoloniusBorrowChecker<'mir, 'tcx: 'mir> {
    pub output_facts: PoloniusOutput,
    pub(crate) borrow_checker_data: RustBorrowCheckerData<'mir, 'tcx>,
}

impl<'mir, 'tcx: 'mir> PoloniusBorrowChecker<'mir, 'tcx> {
    fn ctxt(&self) -> CompilerCtxt<'mir, 'tcx, &Self> {
        CompilerCtxt::new(
            self.borrow_checker_data.body,
            self.borrow_checker_data.tcx,
            self,
        )
    }

    pub fn new<T: BodyAndBorrows<'tcx>>(tcx: ty::TyCtxt<'tcx>, body: &'mir T) -> Self {
        let borrow_checker_data = RustBorrowCheckerData::new(tcx, body);
        let output_facts = Output::compute(
            body.input_facts(),
            polonius_engine::Algorithm::DatafrogOpt,
            true,
        );
        Self {
            borrow_checker_data,
            output_facts,
        }
    }

    pub fn origin_live_on_entry(&self, location: RichLocation) -> Option<BTreeSet<ty::RegionVid>> {
        let origins = match location {
            RichLocation::Start(location) => self.output_facts.origin_live_on_entry.get(
                &self
                    .borrow_checker_data
                    .location_table
                    .start_index(location),
            )?,
            RichLocation::Mid(location) => self
                .output_facts
                .origin_live_on_entry
                .get(&self.borrow_checker_data.location_table.mid_index(location))?,
        };
        Some(origins.iter().map(|r| (*r).into()).collect())
    }

    pub fn loans_live_at(&self, location: RichLocation) -> BTreeSet<ty::RegionVid> {
        let loans = match location {
            RichLocation::Start(location) => self.output_facts.loans_in_scope_at(
                self.borrow_checker_data
                    .location_table
                    .start_index(location),
            ),
            RichLocation::Mid(location) => self
                .output_facts
                .loans_in_scope_at(self.borrow_checker_data.location_table.mid_index(location)),
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

impl<'mir, 'tcx: 'mir> RustBorrowCheckerInterface<'tcx> for PoloniusBorrowChecker<'mir, 'tcx> {
    #[cfg(feature = "visualization")]
    fn override_region_debug_string(&self, region: ty::RegionVid) -> Option<&str> {
        self.borrow_checker_data
            .pretty_printer
            .lookup(region)
            .map(|s| s.as_str())
    }
    #[cfg(not(feature = "visualization"))]
    fn override_region_debug_string(&self, _region: ty::RegionVid) -> Option<&str> {
        None
    }
    fn is_live(&self, node: PcgNode<'tcx>, location: Location) -> bool {
        let regions: Vec<_> = match node {
            PcgNode::Place(place) => place.regions(self.ctxt()).into_iter().collect(),
            PcgNode::LifetimeProjection(region_projection) => {
                vec![region_projection.region(self.ctxt())]
            }
        };
        let live_loans = self.output_facts.loans_in_scope_at(
            self.borrow_checker_data
                .location_table
                .start_index(location),
        );

        let live_origins: BTreeSet<ty::RegionVid> = self
            .output_facts
            .origins_live_at(
                self.borrow_checker_data
                    .location_table
                    .start_index(location),
            )
            .iter()
            .map(|r| (*r).into())
            .collect::<BTreeSet<_>>();
        regions.iter().any(|region| match region {
            PcgRegion::RegionVid(region_vid) => live_loans.iter().any(|loan| {
                if live_origins.contains(region_vid) {
                    return true;
                }
                if self
                    .borrow_checker_data
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

    fn region_infer_ctxt(&self) -> &RegionInferenceContext<'tcx> {
        self.borrow_checker_data.region_cx
    }

    fn location_table(&self) -> &LocationTable {
        self.borrow_checker_data.location_table
    }

    fn polonius_output(&self) -> Option<&PoloniusOutput> {
        Some(&self.output_facts)
    }

    fn borrow_set(&self) -> &BorrowSet<'tcx> {
        self.borrow_checker_data.borrows
    }

    fn input_facts(&self) -> &PoloniusInput {
        self.borrow_checker_data.input_facts
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

    fn borrows_in_scope_at(&self, location: Location, before: bool) -> BitSet<BorrowIndex> {
        self.borrow_checker_data
            .borrows_in_scope_at(location, before)
    }
}

#[deprecated(note = "Use NllBorrowCheckerImpl instead")]
pub type BorrowCheckerImpl<'mir, 'tcx> = NllBorrowCheckerImpl<'mir, 'tcx>;

/// An interface to the results of the NLL borrow-checker analysis.
#[derive(Clone)]
pub struct NllBorrowCheckerImpl<'mir, 'tcx: 'mir> {
    place_liveness: PlaceLiveness<'mir, 'tcx>,
    pub(crate) borrow_checker_data: RustBorrowCheckerData<'mir, 'tcx>,
}

impl<'mir, 'tcx: 'mir> NllBorrowCheckerImpl<'mir, 'tcx> {
    pub fn new<T: BodyAndBorrows<'tcx>>(tcx: ty::TyCtxt<'tcx>, body: &'mir T) -> Self {
        let borrow_checker_data = RustBorrowCheckerData::new(tcx, body);
        let place_liveness = PlaceLiveness::new(CompilerCtxt::new(body.body(), tcx, ()));
        Self {
            borrow_checker_data,
            place_liveness,
        }
    }
}

impl<'tcx> RustBorrowCheckerInterface<'tcx> for NllBorrowCheckerImpl<'_, 'tcx> {
    #[cfg(feature = "visualization")]
    fn override_region_debug_string(&self, region: ty::RegionVid) -> Option<&str> {
        self.borrow_checker_data
            .pretty_printer
            .lookup(region)
            .map(|s| s.as_str())
    }
    #[cfg(not(feature = "visualization"))]
    fn override_region_debug_string(&self, _region: ty::RegionVid) -> Option<&str> {
        None
    }
    fn input_facts(&self) -> &PoloniusInput {
        self.borrow_checker_data.input_facts
    }

    fn borrow_in_scope_at(&self, borrow_index: BorrowIndex, location: Location) -> bool {
        self.borrow_checker_data
            .in_scope_borrows
            .borrow_mut()
            .seek_before_primary_effect(location);
        let result = (*self.borrow_checker_data.in_scope_borrows)
            .borrow()
            .get()
            .contains(borrow_index);
        tracing::debug!(
            "borrow_in_scope_at({:?}, {:?}) = {}",
            borrow_index,
            location,
            result
        );
        result
    }

    fn is_live(&self, node: PcgNode<'tcx>, location: Location) -> bool {
        #[cfg(feature = "custom-rust-toolchain")]
        if let PcgNode::LifetimeProjection(region_projection) = node {
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
        let Some(local) = node.related_maybe_labelled_place().map(|p| p.local()) else {
            return true;
        };
        if local == RETURN_PLACE {
            return true;
        }
        // if let PcgNode::LifetimeProjection(lifetime_projection) = node {
        //     if !self.region_is_live_at(lifetime_projection.region(ctxt), location) {
        //         return false;
        //     }
        // }
        // self.local_is_live_before(local, location)
        self.place_liveness.is_live(local.into(), location)
    }

    fn region_infer_ctxt(&self) -> &RegionInferenceContext<'tcx> {
        self.borrow_checker_data.region_cx
    }

    fn location_table(&self) -> &LocationTable {
        self.borrow_checker_data.location_table
    }

    fn polonius_output(&self) -> Option<&PoloniusOutput> {
        None
    }

    fn borrow_set(&self) -> &BorrowSet<'tcx> {
        self.borrow_checker_data.borrows
    }

    fn origin_contains_loan_at(
        &self,
        region: PcgRegion,
        loan: BorrowIndex,
        _location: Location,
    ) -> bool {
        self.borrow_checker_data
            .region_cx
            .eval_outlives(self.borrow_index_to_region(loan), region.vid().unwrap())
    }

    fn borrows_in_scope_at(&self, location: Location, before: bool) -> BitSet<BorrowIndex> {
        self.borrow_checker_data
            .borrows_in_scope_at(location, before)
    }
}

pub(crate) fn get_reserve_location(borrow: &BorrowData<'_>) -> Location {
    borrow.reserve_location()
}
