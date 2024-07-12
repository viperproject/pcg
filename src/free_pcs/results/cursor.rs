// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc_interface::{
    dataflow::ResultsCursor,
    dataflow::{Analysis, Forward},
    middle::{
        mir::{BasicBlock, Body, Local, Location},
        ty::RegionVid,
    },
};

use crate::{
    combined_pcs::{PcsContext, PcsEngine, PlaceCapabilitySummary},
    free_pcs::{
        engine::FpcsEngine, CapabilitySummary, FreePlaceCapabilitySummary, RepackOp,
        RepackingBridgeSemiLattice,
    },
    rustc_interface,
    utils::PlaceRepacker,
};

pub trait HasFpcs<'mir, 'tcx> {
    fn get_curr_fpcs(&self) -> &FreePlaceCapabilitySummary<'mir, 'tcx>;
}
impl<'mir, 'tcx> HasFpcs<'mir, 'tcx> for FreePlaceCapabilitySummary<'mir, 'tcx> {
    fn get_curr_fpcs(&self) -> &FreePlaceCapabilitySummary<'mir, 'tcx> {
        self
    }
}
impl<'mir, 'tcx> HasFpcs<'mir, 'tcx> for PlaceCapabilitySummary<'mir, 'tcx> {
    fn get_curr_fpcs(&self) -> &FreePlaceCapabilitySummary<'mir, 'tcx> {
        &self.fpcs
    }
}

// trait FpcsEngineLike<'mir, 'tcx, D: FreePlaceCapabilitySummaryLike<'mir, 'tcx>>: Analysis<'tcx, Domain = D>

pub trait HasCgContext<'mir, 'tcx> {
    fn get_cgx(&self) -> std::rc::Rc<PcsContext<'mir, 'tcx>>;
}
impl<'mir, 'tcx> HasCgContext<'mir, 'tcx> for PcsEngine<'mir, 'tcx> {
    fn get_cgx(&self) -> std::rc::Rc<PcsContext<'mir, 'tcx>> {
        self.cgx.clone()
    }
}

type Cursor<'mir, 'tcx, E> = ResultsCursor<'mir, 'tcx, E>;

pub trait HasExtra<T> {
    type ExtraOp;
    fn get_extra(&self) -> T;
    fn bridge_between_stmts(lhs: T, rhs: T) -> (Vec<Self::ExtraOp>, Vec<Self::ExtraOp>);
    fn bridge_terminator(lhs: &T, rhs: T) -> Vec<Self::ExtraOp>;
}

pub struct FreePcsAnalysis<
    'mir,
    'tcx,
    T,
    D: HasFpcs<'mir, 'tcx> + HasExtra<T>,
    E: Analysis<'tcx, Domain = D>,
> {
    cursor: Cursor<'mir, 'tcx, E>,
    curr_stmt: Option<Location>,
    end_stmt: Option<Location>,
    _marker: std::marker::PhantomData<T>,
}

impl<'mir, 'tcx, T, D: HasFpcs<'mir, 'tcx> + HasExtra<T>, E: Analysis<'tcx, Domain = D>>
    FreePcsAnalysis<'mir, 'tcx, T, D, E>
{
    pub(crate) fn new(cursor: Cursor<'mir, 'tcx, E>) -> Self {
        Self {
            cursor,
            curr_stmt: None,
            end_stmt: None,
            _marker: std::marker::PhantomData,
        }
    }

    // pub fn universal_constraints(&self) -> Vec<(Vec<(RegionVid, Local)>, Vec<(RegionVid, Local)>)> where E: HasCgContext<'mir, 'tcx> {
    //     self.cursor.analysis().get_cgx().signature_constraints()
    // }

    pub fn analysis_for_bb(&mut self, block: BasicBlock) {
        self.cursor.seek_to_block_start(block);
        let end_stmt = self.body().terminator_loc(block).successor_within_block();
        self.curr_stmt = Some(Location {
            block,
            statement_index: 0,
        });
        self.end_stmt = Some(end_stmt);
    }

    fn body(&self) -> &'mir Body<'tcx> {
        self.repacker().body()
    }

    pub fn repacker(&self) -> PlaceRepacker<'mir, 'tcx> {
        self.cursor.get().get_curr_fpcs().repacker
    }

    pub fn initial_state(&self) -> &CapabilitySummary<'tcx> {
        &self.cursor.get().get_curr_fpcs().after
    }
    pub fn next(&mut self, exp_loc: Location) -> FreePcsLocation<'tcx, T, D::ExtraOp> {
        let location = self.curr_stmt.unwrap();
        assert_eq!(location, exp_loc);
        assert!(location < self.end_stmt.unwrap());
        self.curr_stmt = Some(location.successor_within_block());

        let after = self.cursor.get().get_curr_fpcs().after.clone();
        let extra_after = self.cursor.get().get_extra();
        self.cursor.seek_after_primary_effect(location);
        let c = self.cursor.get().get_curr_fpcs();
        let (repacks_start, repacks_middle) = c.repack_ops(&after);
        let (extra_start, extra_middle) =
            D::bridge_between_stmts(extra_after, self.cursor.get().get_extra());
        FreePcsLocation {
            location,
            state: c.after.clone(),
            repacks_start,
            repacks_middle,
            extra_start,
            extra_middle,
            extra: self.cursor.get().get_extra(),
        }
    }
    pub fn terminator(&mut self) -> FreePcsTerminator<'tcx, T, D::ExtraOp> {
        let location = self.curr_stmt.unwrap();
        assert!(location == self.end_stmt.unwrap());
        self.curr_stmt = None;
        self.end_stmt = None;

        // TODO: cleanup
        let rp: PlaceRepacker = self.repacker();
        let extra = self.cursor.get().get_extra();
        let state = self.cursor.get().get_curr_fpcs().clone();
        let block = &self.body()[location.block];
        let succs = block
            .terminator()
            .successors()
            .map(|succ| {
                // Get repacks
                let entry_set = self.cursor.results().entry_set_for_block(succ);
                let to = entry_set.get_curr_fpcs();
                let extra_to = entry_set.get_extra();
                FreePcsLocation {
                    location: Location {
                        block: succ,
                        statement_index: 0,
                    },
                    state: to.after.clone(),
                    repacks_start: state.after.bridge(&to.after, rp),
                    repacks_middle: Vec::new(),
                    extra: entry_set.get_extra(),
                    extra_start: D::bridge_terminator(&extra, extra_to),
                    extra_middle: Vec::new(),
                }
            })
            .collect();
        FreePcsTerminator { succs }
    }

    /// Recommended interface.
    /// Does *not* require that one calls `analysis_for_bb` first
    pub fn get_all_for_bb(&mut self, block: BasicBlock) -> FreePcsBasicBlock<'tcx, T, D::ExtraOp> {
        self.analysis_for_bb(block);
        let mut statements = Vec::new();
        while self.curr_stmt.unwrap() != self.end_stmt.unwrap() {
            let stmt = self.next(self.curr_stmt.unwrap());
            statements.push(stmt);
        }
        let terminator = self.terminator();
        FreePcsBasicBlock {
            statements,
            terminator,
        }
    }
}

pub struct FreePcsBasicBlock<'tcx, T, A> {
    pub statements: Vec<FreePcsLocation<'tcx, T, A>>,
    pub terminator: FreePcsTerminator<'tcx, T, A>,
}

#[derive(Debug)]
pub struct FreePcsLocation<'tcx, T, A> {
    pub location: Location,
    /// Repacks before the statement
    pub repacks_start: Vec<RepackOp<'tcx>>,
    /// Repacks in the middle of the statement
    pub repacks_middle: Vec<RepackOp<'tcx>>,
    /// State after the statement
    pub state: CapabilitySummary<'tcx>,
    pub extra_start: Vec<A>,
    pub extra_middle: Vec<A>,
    pub extra: T,
}

#[derive(Debug)]
pub struct FreePcsTerminator<'tcx, T, A> {
    pub succs: Vec<FreePcsLocation<'tcx, T, A>>,
}
