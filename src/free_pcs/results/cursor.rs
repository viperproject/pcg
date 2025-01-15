// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::rustc_interface::{
    dataflow::Analysis,
    dataflow::ResultsCursor,
    middle::mir::{BasicBlock, Body, Location},
};

use crate::{
    borrows::{borrows_visitor::DebugCtx, engine::BorrowsStates},
    combined_pcs::PlaceCapabilitySummary,
    free_pcs::{
        CapabilitySummary, FreePlaceCapabilitySummary, RepackOp, RepackingBridgeSemiLattice,
    },
    utils::PlaceRepacker,
    BorrowsBridge,
};

pub trait HasPcs<'mir, 'tcx> {
    fn get_curr_fpcg(&self) -> &FreePlaceCapabilitySummary<'mir, 'tcx>;
    fn get_borrows_states(&self) -> &BorrowsStates<'tcx>;
}

impl<'mir, 'tcx> HasPcs<'mir, 'tcx> for PlaceCapabilitySummary<'mir, 'tcx> {
    fn get_curr_fpcg(&self) -> &FreePlaceCapabilitySummary<'mir, 'tcx> {
        &self.owned_pcg()
    }
    fn get_borrows_states(&self) -> &BorrowsStates<'tcx> {
        &self.borrow_pcg().states
    }
}

type Cursor<'mir, 'tcx, E> = ResultsCursor<'mir, 'tcx, E>;

pub struct FreePcsAnalysis<'mir, 'tcx, D: HasPcs<'mir, 'tcx>, E: Analysis<'tcx, Domain = D>> {
    pub cursor: Cursor<'mir, 'tcx, E>,
    curr_stmt: Option<Location>,
    end_stmt: Option<Location>,
}

impl<'mir, 'tcx, D: HasPcs<'mir, 'tcx>, E: Analysis<'tcx, Domain = D>>
    FreePcsAnalysis<'mir, 'tcx, D, E>
{
    pub(crate) fn new(cursor: Cursor<'mir, 'tcx, E>) -> Self {
        Self {
            cursor,
            curr_stmt: None,
            end_stmt: None,
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
        self.cursor.get().get_curr_fpcg().repacker
    }

    pub fn initial_state(&self) -> &CapabilitySummary<'tcx> {
        &self.cursor.get().get_curr_fpcg().post_main
    }

    /// Returns the free pcs for the location `exp_loc` and iterates the cursor
    /// to the *end* of that location.
    pub fn next(&mut self, exp_loc: Location) -> FreePcsLocation<'tcx> {
        let location = self.curr_stmt.unwrap();
        assert_eq!(location, exp_loc);
        assert!(location < self.end_stmt.unwrap());

        let state = self.cursor.get();

        let after = state.get_curr_fpcg().post_main.clone();
        let curr_borrows = state.get_borrows_states().clone();

        self.cursor.seek_after_primary_effect(location);

        let state = self.cursor.get();
        let curr_fpcs = state.get_curr_fpcg();
        let (repacks_start, repacks_middle) = curr_fpcs.repack_ops(&after);

        let (extra_start, extra_middle) = curr_borrows.bridge_between_stmts(
            state.get_borrows_states(),
            DebugCtx::new(location),
            self.repacker(),
        );

        let result = FreePcsLocation {
            location,
            states: CapabilitySummaries {
                before_start: curr_fpcs.pre_operands.clone(),
                before_after: curr_fpcs.post_operands.clone(),
                start: curr_fpcs.pre_main.clone(),
                after: curr_fpcs.post_main.clone(),
            },
            repacks_start,
            repacks_middle,
            extra_start,
            extra_middle,
            borrows: state.get_borrows_states().clone(),
        };

        self.curr_stmt = Some(location.successor_within_block());

        result
    }
    pub fn terminator(&mut self) -> FreePcsTerminator<'tcx> {
        let location = self.curr_stmt.unwrap();
        assert!(location == self.end_stmt.unwrap());
        self.curr_stmt = None;
        self.end_stmt = None;

        // TODO: cleanup
        let rp: PlaceRepacker = self.repacker();
        let state = self.cursor.get().get_curr_fpcg().clone();
        let block = &self.body()[location.block];
        let succs = block
            .terminator()
            .successors()
            .map(|succ| {
                // Get repacks
                let entry_set = self.cursor.results().entry_set_for_block(succ);
                let to = entry_set.get_curr_fpcg();
                FreePcsLocation {
                    location: Location {
                        block: succ,
                        statement_index: 0,
                    },
                    states: CapabilitySummaries {
                        before_start: to.pre_operands.clone(),
                        before_after: to.post_operands.clone(),
                        start: to.pre_main.clone(),
                        after: to.post_main.clone(),
                    },
                    repacks_start: state.post_main.bridge(&to.post_main, rp),
                    repacks_middle: Vec::new(),
                    borrows: entry_set.get_borrows_states().clone(),
                    extra_start: BorrowsBridge::new(),
                    extra_middle: BorrowsBridge::new(),
                }
            })
            .collect();
        FreePcsTerminator { succs }
    }

    /// Recommended interface.
    /// Does *not* require that one calls `analysis_for_bb` first
    pub fn get_all_for_bb(&mut self, block: BasicBlock) -> FreePcsBasicBlock<'tcx> {
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

pub struct FreePcsBasicBlock<'tcx> {
    pub statements: Vec<FreePcsLocation<'tcx>>,
    pub terminator: FreePcsTerminator<'tcx>,
}

#[derive(Debug)]
pub struct CapabilitySummaries<'tcx> {
    pub before_start: CapabilitySummary<'tcx>,
    pub before_after: CapabilitySummary<'tcx>,
    pub start: CapabilitySummary<'tcx>,
    pub after: CapabilitySummary<'tcx>,
}

#[derive(Debug)]
pub struct FreePcsLocation<'tcx> {
    pub location: Location,
    /// Repacks before the statement
    pub repacks_start: Vec<RepackOp<'tcx>>,
    /// Repacks in the middle of the statement
    pub repacks_middle: Vec<RepackOp<'tcx>>,
    pub states: CapabilitySummaries<'tcx>,
    pub extra_start: BorrowsBridge<'tcx>,
    pub extra_middle: BorrowsBridge<'tcx>,
    pub borrows: BorrowsStates<'tcx>,
}

#[derive(Debug)]
pub struct FreePcsTerminator<'tcx> {
    pub succs: Vec<FreePcsLocation<'tcx>>,
}
