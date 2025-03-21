// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::rc::Rc;

use derive_more::Deref;

use crate::{
    borrow_pcg::{
        action::BorrowPCGActionKind, borrow_pcg_edge::BorrowPCGEdge,
        latest::Latest,
    },
    combined_pcs::{successor_blocks, EvalStmtPhase, PCGEngine, Pcg, PcgError, PcgSuccessor},
    rustc_interface::{
        data_structures::fx::FxHashSet,
        dataflow::PCGAnalysis,
        index::IndexVec,
        middle::{
            mir::{self, BasicBlock, Body, Location},
            ty::TyCtxt,
        },
        mir_dataflow::ResultsCursor,
    },
    utils::{display::DebugLines, validity::HasValidityCheck, Place},
};

use crate::borrow_pcg::action::actions::BorrowPCGActions;
use crate::utils::eval_stmt_data::EvalStmtData;
use crate::{
    borrow_pcg::engine::BorrowsStates,
    combined_pcs::PlaceCapabilitySummary,
    free_pcs::{CapabilitySummary, RepackOp, RepackingBridgeSemiLattice},
    utils::PlaceRepacker,
};

pub trait HasPcg<'mir, 'tcx> {
    fn get_pcg(&self) -> Result<&Pcg<'mir, 'tcx>, PcgError>;
}

impl<'mir, 'tcx> HasPcg<'mir, 'tcx> for PlaceCapabilitySummary<'mir, 'tcx> {
    fn get_pcg(&self) -> Result<&Pcg<'mir, 'tcx>, PcgError> {
        self.pcg.as_ref().map_err(|e| e.clone())
    }
}

type Cursor<'mir, 'tcx, E> = ResultsCursor<'mir, 'tcx, E>;

pub struct FreePcsAnalysis<'mir, 'tcx: 'mir> {
    pub cursor: Cursor<'mir, 'tcx, PCGAnalysis<PCGEngine<'mir, 'tcx>>>,
    curr_stmt: Option<Location>,
    end_stmt: Option<Location>,
}

impl<'mir, 'tcx> FreePcsAnalysis<'mir, 'tcx> {
    pub(crate) fn new(cursor: Cursor<'mir, 'tcx, PCGAnalysis<PCGEngine<'mir, 'tcx>>>) -> Self {
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
        self.cursor.analysis().0.repacker
    }

    /// Returns the free pcs for the location `exp_loc` and iterates the cursor
    /// to the *end* of that location.
    ///
    /// This function may return `None` if the PCG did not analyze this block.
    /// This could happen, for example, if the block would only be reached when unwinding from a panic.
    fn next(&mut self, exp_loc: Location) -> Result<Option<PcgLocation<'tcx>>, PcgError> {
        let location = self.curr_stmt.unwrap();
        assert_eq!(location, exp_loc);
        assert!(location < self.end_stmt.unwrap());

        self.cursor.seek_after_primary_effect(location);

        let state = self.cursor.get();

        let pcg = state.get_pcg()?;

        let repack_ops = pcg.owned.repack_ops().map_err(|mut e| {
            e.add_context(format!("At {:?}", location));
            e
        })?;

        let result = PcgLocation {
            location,
            borrow_pcg_actions: pcg.borrow.actions.clone(),
            states: pcg
                .owned
                .data
                .states
                .0
                .clone()
                .map(|s| Rc::new(s.as_ref().as_ref().unwrap().clone())),
            repacks_start: repack_ops.start,
            repacks_middle: repack_ops.middle,
            borrows: pcg.borrow.data.states.0.clone(),
        };

        self.curr_stmt = Some(location.successor_within_block());

        Ok(Some(result))
    }
    pub(crate) fn terminator(&mut self) -> Result<PcgTerminator<'tcx>, PcgError> {
        let location = self.curr_stmt.unwrap();
        assert!(location == self.end_stmt.unwrap());
        self.curr_stmt = None;
        self.end_stmt = None;

        let from_pcg = self.cursor.get().get_pcg()?;

        // TODO: cleanup
        let rp: PlaceRepacker = self.repacker();
        let block = &self.body()[location.block];

        // Currently we ignore blocks that are only reached via panics
        let succs = successor_blocks(block.terminator())
            .into_iter()
            .filter(|succ| {
                self.cursor
                    .results()
                    .analysis
                    .0
                    .reachable_blocks
                    .contains(*succ)
            })
            .map(|succ| {
                // Get repacks
                let entry_set = self.cursor.results().entry_set_for_block(succ);
                let to = entry_set.get_pcg()?;
                Ok(PcgSuccessor::new(
                    succ,
                    from_pcg
                        .owned
                        .data
                        .unwrap(EvalStmtPhase::PostMain)
                        .bridge(to.owned.data.entry_state.as_ref().as_ref().unwrap(), rp)
                        .unwrap(),
                    {
                        let mut actions = BorrowPCGActions::new();
                        let self_abstraction_edges = from_pcg.borrow.data.states
                            [EvalStmtPhase::PostMain]
                            .graph()
                            .abstraction_edges()
                            .collect::<FxHashSet<_>>();
                        for abstraction in to.borrow.data.entry_state.graph().abstraction_edges() {
                            if !self_abstraction_edges.contains(&abstraction) {
                                actions.push(
                                    BorrowPCGActionKind::AddEdge {
                                        edge: BorrowPCGEdge::new(
                                            abstraction.value.clone().into(),
                                            abstraction.conditions,
                                        ),
                                        for_exclusive: true,
                                    }
                                    .into(),
                                );
                            }
                        }
                        actions
                    },
                    to.borrow.data.entry_state.clone(),
                ))
            })
            .collect::<Result<Vec<_>, PcgError>>()?;
        Ok(PcgTerminator { succs })
    }

    /// Obtains the results of the dataflow analysis for all blocks.
    ///
    /// This is rather expensive to compute and may take a lot of memory. You
    /// may want to consider using `get_all_for_bb` instead.
    pub fn results_for_all_blocks(&mut self) -> Result<PcgBasicBlocks<'tcx>, PcgError> {
        let mut result = IndexVec::new();
        for block in self.body().basic_blocks.indices() {
            result.push(self.get_all_for_bb(block)?);
        }
        Ok(PcgBasicBlocks(result))
    }

    fn analysis(&self) -> &PCGEngine<'mir, 'tcx> {
        &self.cursor.results().analysis.0
    }

    pub fn first_error(&self) -> Option<PcgError> {
        self.analysis().first_error.error().cloned()
    }

    /// Recommended interface.
    /// Does *not* require that one calls `analysis_for_bb` first
    /// This function may return `None` if the PCG did not analyze this block.
    /// This could happen, for example, if the block would only be reached when unwinding from a panic.
    pub fn get_all_for_bb(
        &mut self,
        block: BasicBlock,
    ) -> Result<Option<PcgBasicBlock<'tcx>>, PcgError> {
        if !self.analysis().reachable_blocks.contains(block) {
            return Ok(None);
        }
        self.analysis_for_bb(block);
        let mut statements = Vec::new();
        while self.curr_stmt.unwrap() != self.end_stmt.unwrap() {
            let stmt = self.next(self.curr_stmt.unwrap())?;
            if let Some(stmt) = stmt {
                statements.push(stmt);
            } else {
                return Ok(None);
            }
        }
        let terminator = self.terminator()?;
        Ok(Some(PcgBasicBlock {
            statements,
            terminator,
        }))
    }
}

#[derive(Deref)]
pub struct PcgBasicBlocks<'tcx>(IndexVec<BasicBlock, Option<PcgBasicBlock<'tcx>>>);

impl<'tcx> PcgBasicBlocks<'tcx> {
    pub fn get_statement(&self, location: Location) -> Option<&PcgLocation<'tcx>> {
        if let Some(pcg_block) = &self.0[location.block] {
            pcg_block.statements.get(location.statement_index)
        } else {
            None
        }
    }

    pub fn all_place_aliases<'mir>(
        &self,
        place: mir::Place<'tcx>,
        body: &'mir Body<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> FxHashSet<mir::Place<'tcx>> {
        let mut result = FxHashSet::default();
        for block in self.0.iter() {
            if let Some(pcg_block) = &block {
                for stmt in pcg_block.statements.iter() {
                    result.extend(stmt.aliases(place, body, tcx));
                }
            }
        }
        result
    }
}

pub struct PcgBasicBlock<'tcx> {
    pub statements: Vec<PcgLocation<'tcx>>,
    pub terminator: PcgTerminator<'tcx>,
}

impl<'tcx> PcgBasicBlock<'tcx> {
    pub fn debug_lines(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Vec<String> {
        let mut result = Vec::new();
        for stmt in self.statements.iter() {
            for phase in EvalStmtPhase::phases() {
                for line in stmt.debug_lines(phase, repacker) {
                    result.push(format!("{:?} {}: {}", stmt.location, phase, line));
                }
            }
        }
        for term_succ in self.terminator.succs.iter() {
            for line in term_succ.debug_lines(repacker) {
                result.push(format!("Terminator({:?}): {}", term_succ.block(), line));
            }
        }
        result
    }
}

pub type CapabilitySummaries<'tcx> = EvalStmtData<Rc<CapabilitySummary<'tcx>>>;

#[derive(Debug)]
pub struct PcgLocation<'tcx> {
    pub location: Location,
    /// Repacks before the statement
    pub repacks_start: Vec<RepackOp<'tcx>>,
    /// Repacks in the middle of the statement
    pub repacks_middle: Vec<RepackOp<'tcx>>,
    pub states: CapabilitySummaries<'tcx>,
    pub borrows: BorrowsStates<'tcx>,
    pub(crate) borrow_pcg_actions: EvalStmtData<BorrowPCGActions<'tcx>>,
}

impl<'tcx> DebugLines<PlaceRepacker<'_, 'tcx>> for Vec<RepackOp<'tcx>> {
    fn debug_lines(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> Vec<String> {
        self.iter().map(|r| format!("{:?}", r)).collect()
    }
}

impl<'tcx> HasValidityCheck<'tcx> for PcgLocation<'tcx> {
    fn check_validity(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Result<(), String> {
        self.borrows.check_validity(repacker)
    }
}

impl<'tcx> PcgLocation<'tcx> {
    pub fn borrow_pcg_actions(&self, phase: EvalStmtPhase) -> &BorrowPCGActions<'tcx> {
        &self.borrow_pcg_actions[phase]
    }

    pub fn aliases<'mir>(
        &self,
        place: impl Into<Place<'tcx>>,
        body: &'mir Body<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> FxHashSet<mir::Place<'tcx>> {
        let place: Place<'tcx> = place.into();
        let repacker = PlaceRepacker::new(body, tcx);
        self.borrows
            .post_main
            .graph()
            .aliases(place.with_inherent_region(repacker).into(), repacker)
            .into_iter()
            .flat_map(|p| p.as_current_place())
            .map(|p| p.to_rust_place(repacker))
            .collect()
    }

    pub fn latest(&self) -> &Latest<'tcx> {
        &self.borrows.post_main.latest
    }

    pub(crate) fn debug_lines(
        &self,
        phase: EvalStmtPhase,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Vec<String> {
        let mut result = self.states[phase].debug_lines(repacker);
        for action in self.borrow_pcg_actions[phase].iter() {
            result.push(action.debug_line(repacker));
        }
        result.extend(self.borrows[phase].debug_lines(repacker));
        for line in self.repacks_start.debug_lines(repacker) {
            result.push(format!("Repacks Start: {}", line));
        }
        for line in self.repacks_middle.debug_lines(repacker) {
            result.push(format!("Repacks Middle: {}", line));
        }
        result
    }
}

#[derive(Debug)]
pub struct PcgTerminator<'tcx> {
    pub succs: Vec<PcgSuccessor<'tcx>>,
}
