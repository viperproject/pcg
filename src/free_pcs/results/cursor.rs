// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    borrows::{
        engine::{BorrowsDomain, EvalStmtData},
        latest::Latest,
    },
    combined_pcs::EvalStmtPhase,
    rustc_interface::{
        dataflow::{Analysis, ResultsCursor},
        middle::mir::{BasicBlock, Body, Location},
    },
    utils::{display::DebugLines, validity::HasValidityCheck},
    BorrowPCGActions,
};

use crate::{
    borrows::engine::BorrowsStates,
    combined_pcs::PlaceCapabilitySummary,
    free_pcs::{
        CapabilitySummary, FreePlaceCapabilitySummary, RepackOp, RepackingBridgeSemiLattice,
    },
    utils::PlaceRepacker,
    BorrowsBridge,
};

pub trait HasPcg<'mir, 'tcx> {
    fn get_curr_fpcg(&self) -> &FreePlaceCapabilitySummary<'mir, 'tcx>;
    fn get_curr_borrow_pcg(&self) -> &BorrowsDomain<'mir, 'tcx>;
}

impl<'mir, 'tcx> HasPcg<'mir, 'tcx> for PlaceCapabilitySummary<'mir, 'tcx> {
    fn get_curr_fpcg(&self) -> &FreePlaceCapabilitySummary<'mir, 'tcx> {
        &self.owned_pcg()
    }

    fn get_curr_borrow_pcg(&self) -> &BorrowsDomain<'mir, 'tcx> {
        &self.borrow_pcg()
    }
}

type Cursor<'mir, 'tcx, E> = ResultsCursor<'mir, 'tcx, E>;

pub struct FreePcsAnalysis<'mir, 'tcx, D, E: Analysis<'tcx, Domain = D>> {
    pub cursor: Cursor<'mir, 'tcx, E>,
    curr_stmt: Option<Location>,
    end_stmt: Option<Location>,
}

impl<'mir, 'tcx, D: HasPcg<'mir, 'tcx>, E: Analysis<'tcx, Domain = D>>
    FreePcsAnalysis<'mir, 'tcx, D, E>
{
    pub(crate) fn new(cursor: Cursor<'mir, 'tcx, E>) -> Self {
        Self {
            cursor,
            curr_stmt: None,
            end_stmt: None,
        }
    }

    pub(crate) fn analysis_for_bb(&mut self, block: BasicBlock) {
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

    /// Returns the free pcs for the location `exp_loc` and iterates the cursor
    /// to the *end* of that location.
    pub(crate) fn next(&mut self, exp_loc: Location) -> FreePcsLocation<'tcx> {
        let location = self.curr_stmt.unwrap();
        assert_eq!(location, exp_loc);
        assert!(location < self.end_stmt.unwrap());

        let state = self.cursor.get();

        let prev_post_main = state.get_curr_fpcg().post_main().clone();

        self.cursor.seek_after_primary_effect(location);

        let state = self.cursor.get();
        let curr_fpcs = state.get_curr_fpcg();
        let curr_borrows = state.get_curr_borrow_pcg();
        let repack_ops = curr_fpcs.repack_ops(&prev_post_main).unwrap_or_else(|e| {
            panic!(
                "Repack ops error for cursor transition {:?} -> {:?}: {:?}",
                location,
                location.successor_within_block(),
                e
            );
        });

        let (extra_start, extra_middle) = curr_borrows.get_bridge();

        let result = FreePcsLocation {
            location,
            actions: curr_borrows.actions.clone(),
            states: curr_fpcs.summaries.clone(),
            repacks_start: repack_ops.start,
            repacks_middle: repack_ops.middle,
            extra_start,
            extra_middle,
            borrows: curr_borrows.states.clone(),
        };

        self.curr_stmt = Some(location.successor_within_block());

        result
    }
    pub(crate) fn terminator(&mut self) -> FreePcsTerminator<'tcx> {
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
                    actions: entry_set.get_curr_borrow_pcg().actions.clone(),
                    states: to.summaries.clone(),
                    repacks_start: state.post_main().bridge(&to.post_main(), rp).unwrap(),
                    repacks_middle: Vec::new(),
                    borrows: entry_set.get_curr_borrow_pcg().states.clone(),
                    // TODO: It seems like extra_start should be similar to repacks_start
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

impl<'tcx> FreePcsBasicBlock<'tcx> {
    pub fn debug_lines(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Vec<String> {
        let mut result = Vec::new();
        for stmt in self.statements.iter() {
            for phase in EvalStmtPhase::phases() {
                for line in stmt.debug_lines(phase, repacker) {
                    result.push(format!("{:?} {}: {}", stmt.location, phase, line));
                }
            }
        }
        result
    }
}

pub type CapabilitySummaries<'tcx> = EvalStmtData<CapabilitySummary<'tcx>>;

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
    pub(crate) actions: EvalStmtData<BorrowPCGActions<'tcx>>,
}

impl<'tcx> HasValidityCheck<'tcx> for FreePcsLocation<'tcx> {
    fn check_validity(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Result<(), String> {
        self.borrows.check_validity(repacker)
    }
}

impl<'tcx> FreePcsLocation<'tcx> {
    pub fn latest(&self) -> &Latest<'tcx> {
        &self.borrows.post_main.latest
    }

    pub(crate) fn debug_lines(
        &self,
        phase: EvalStmtPhase,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Vec<String> {
        let mut result = self.states[phase].debug_lines(repacker);
        for action in self.actions[phase].iter() {
            result.push(action.debug_line(repacker));
        }
        result.extend(self.borrows[phase].debug_lines(repacker));
        result
    }
}

#[derive(Debug)]
pub struct FreePcsTerminator<'tcx> {
    pub succs: Vec<FreePcsLocation<'tcx>>,
}
