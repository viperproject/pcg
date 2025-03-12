use crate::borrow_pcg::coupling_graph_constructor::BorrowCheckerInterface;
use crate::borrow_pcg::region_projection::PCGRegion;
use crate::borrow_pcg::visitor::extract_regions;
use crate::combined_pcs::PCGNode;
use crate::rustc_interface::borrowck::{BorrowSet, RegionInferenceContext};
use crate::rustc_interface::dataflow::compute_fixpoint;
use crate::rustc_interface::middle::mir::{self, Location};
use crate::rustc_interface::mir_dataflow::{impls::MaybeLiveLocals, ResultsCursor};
use crate::utils::maybe_remote::MaybeRemotePlace;
use crate::utils::PlaceRepacker;
use std::cell::{RefCell, RefMut};
use std::rc::Rc;

#[derive(Clone)]
pub(crate) struct BorrowCheckerImpl<'mir, 'tcx> {
    repacker: PlaceRepacker<'mir, 'tcx>,
    cursor: Rc<RefCell<ResultsCursor<'mir, 'tcx, MaybeLiveLocals>>>,
    region_cx: &'mir RegionInferenceContext<'tcx>,

    // TODO: Use this to determine when two-phase borrows are activated and
    // update the PCG accordingly
    #[allow(unused)]
    borrows: &'mir BorrowSet<'tcx>,
}

impl<'mir, 'tcx> BorrowCheckerImpl<'mir, 'tcx> {
    pub(crate) fn new(
        repacker: PlaceRepacker<'mir, 'tcx>,
        region_cx: &'mir RegionInferenceContext<'tcx>,
        borrows: &'mir BorrowSet<'tcx>,
    ) -> Self {
        let cursor = compute_fixpoint(MaybeLiveLocals, repacker.tcx(), repacker.body())
            .into_results_cursor(repacker.body());
        Self {
            repacker,
            cursor: Rc::new(RefCell::new(cursor)),
            region_cx,
            borrows,
        }
    }
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

impl<'tcx> BorrowCheckerInterface<'tcx> for BorrowCheckerImpl<'_, 'tcx> {
    fn outlives(&self, sup: PCGRegion, sub: PCGRegion) -> bool {
        match (sup, sub) {
            (PCGRegion::RegionVid(sup), PCGRegion::RegionVid(sub)) => {
                self.region_cx.eval_outlives(sup, sub)
            }
            (PCGRegion::ReStatic, _) => true,
            _ => false,
        }
    }

    fn is_live(&self, node: PCGNode<'tcx>, location: Location) -> bool {
        let local = match node {
            PCGNode::RegionProjection(rp) => {
                if let Some(local) = rp.local() {
                    local
                } else {
                    todo!()
                }
            }
            PCGNode::Place(MaybeRemotePlace::Local(p)) => p.local(),
            _ => {
                return true;
            }
        };
        let local_ty = self.repacker.body().local_decls[local].ty;
        let regions = extract_regions(local_ty, self.repacker);

        // Be conservative: regions within the struct may be live.
        if regions.len() > 1 || (regions.len() == 1 && !local_ty.is_ref()) {
            return true;
        }
        let mut cursor = self.cursor.as_ref().borrow_mut();
        cursor.seek_before_primary_effect(location);
        cursor_contains_local(cursor, local)
    }

    #[rustversion::since(2024-12-14)]
    fn twophase_borrow_activations(
        &self,
        location: Location,
    ) -> std::collections::BTreeSet<Location> {
        self.borrows.activation_map()[&location]
            .iter()
            .map(|idx| self.borrows[*idx].reserve_location())
            .collect()
    }

    #[rustversion::before(2024-12-14)]
    fn twophase_borrow_activations(
        &self,
        location: Location,
    ) -> std::collections::BTreeSet<Location> {
        self.borrows.activation_map[&location]
            .iter()
            .map(|idx| self.borrows[*idx].reserve_location)
            .collect()
    }
}
