// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{alloc::Allocator, rc::Rc};

use derive_more::Deref;

use crate::{
    action::PcgActions,
    borrow_pcg::{
        action::BorrowPCGActionKind,
        borrow_pcg_edge::{BorrowPCGEdge, BorrowPCGEdgeRef},
        latest::Latest,
        region_projection::{HasRegionProjections, MaybeRemoteRegionProjectionBase},
    },
    pcg::{successor_blocks, EvalStmtPhase, PCGNode, Pcg, PcgEngine, PcgError, PcgSuccessor},
    rustc_interface::{
        data_structures::fx::FxHashSet,
        dataflow::AnalysisEngine,
        index::IndexVec,
        middle::{
            mir::{self, BasicBlock, Body, Location},
            ty::TyCtxt,
        },
        mir_dataflow::ResultsCursor,
    },
    utils::{
        display::DebugLines, domain_data::DomainDataStates, validity::HasValidityCheck, Place,
    },
};

use crate::borrow_pcg::action::actions::BorrowPCGActions;
use crate::utils::eval_stmt_data::EvalStmtData;
use crate::{
    free_pcs::{CapabilityLocals, RepackOp},
    utils::CompilerCtxt,
};

type Cursor<'mir, 'tcx, E> = ResultsCursor<'mir, 'tcx, E>;

pub struct PcgAnalysis<'mir, 'tcx: 'mir, A: Allocator + Copy> {
    pub cursor: Cursor<'mir, 'tcx, AnalysisEngine<PcgEngine<'mir, 'tcx, A>>>,
    curr_stmt: Option<Location>,
    end_stmt: Option<Location>,
}

impl<'mir, 'tcx, A: Allocator + Copy> PcgAnalysis<'mir, 'tcx, A> {
    pub(crate) fn new(
        cursor: Cursor<'mir, 'tcx, AnalysisEngine<PcgEngine<'mir, 'tcx, A>>>,
    ) -> Self {
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
        self.ctxt().body()
    }

    pub fn ctxt(&self) -> CompilerCtxt<'mir, 'tcx> {
        self.cursor.analysis().0.ctxt
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

        let data = state.data.as_ref().map_err(|e| e.clone())?;

        let result = PcgLocation {
            location,
            actions: data.actions.clone(),
            states: data.pcg.states.to_owned(),
        };

        self.curr_stmt = Some(location.successor_within_block());

        Ok(Some(result))
    }
    pub(crate) fn terminator(&mut self) -> Result<PcgTerminator<'tcx>, PcgError> {
        let location = self.curr_stmt.unwrap();
        assert!(location == self.end_stmt.unwrap());
        self.curr_stmt = None;
        self.end_stmt = None;

        let from_pcg = &self.cursor.get().data()?.pcg;
        let from_post_main = from_pcg.states[EvalStmtPhase::PostMain].clone();
        let self_abstraction_edges = from_post_main
            .borrow
            .graph()
            .abstraction_edges()
            .collect::<FxHashSet<_>>();

        let ctxt: CompilerCtxt = self.ctxt();
        let block = &self.body()[location.block];

        let succ_blocks = successor_blocks(block.terminator())
            .into_iter()
            .filter(|succ| {
                self.cursor
                    .analysis()
                    .0
                    .reachable_blocks
                    .contains(succ.index())
            })
            .collect::<Vec<_>>();
        let succs = succ_blocks
            .into_iter()
            .map(|succ| {
                self.cursor.seek_to_block_start(succ);
                let to = &self.cursor.get().data()?.pcg;

                let owned_bridge = from_post_main
                    .owned
                    .bridge(&to.entry_state.owned, &from_post_main.capabilities, ctxt)
                    .unwrap();

                let mut borrow_actions = BorrowPCGActions::new();
                for abstraction in to.entry_state.borrow.graph().abstraction_edges() {
                    if !self_abstraction_edges.contains(&abstraction) {
                        borrow_actions.push(
                            BorrowPCGActionKind::AddEdge {
                                edge: BorrowPCGEdge::new(
                                    abstraction.value.clone().into(),
                                    abstraction.conditions,
                                ),
                                for_exclusive: true,
                            }
                            .into(),
                            ctxt,
                        );
                    }
                }

                let mut actions: PcgActions<'tcx> = owned_bridge.into();
                actions.extend(borrow_actions.into());

                Ok(PcgSuccessor::new(
                    succ,
                    actions,
                    to.entry_state.borrow.clone().into(),
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

    fn analysis(&self) -> &PcgEngine<'mir, 'tcx, A> {
        &self.cursor.analysis().0
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
        if !self.analysis().reachable_blocks.contains(block.index()) {
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

    fn aggregate<'mir, T: std::hash::Hash + std::cmp::Eq>(
        &self,
        f: impl Fn(&PcgLocation<'tcx>) -> FxHashSet<T>,
    ) -> FxHashSet<T> {
        let mut result = FxHashSet::default();
        for block in self.0.iter() {
            if let Some(pcg_block) = &block {
                for stmt in pcg_block.statements.iter() {
                    result.extend(f(stmt));
                }
            }
        }
        result
    }

    pub fn all_place_aliases<'mir>(
        &self,
        place: mir::Place<'tcx>,
        body: &'mir Body<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> FxHashSet<mir::Place<'tcx>> {
        self.aggregate(|stmt| stmt.aliases(place, body, tcx))
    }
}

pub struct PcgBasicBlock<'tcx> {
    pub statements: Vec<PcgLocation<'tcx>>,
    pub terminator: PcgTerminator<'tcx>,
}

impl<'tcx> PcgBasicBlock<'tcx> {
    pub fn debug_lines(&self, repacker: CompilerCtxt<'_, 'tcx>) -> Vec<String> {
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

pub type CapabilitySummaries<'tcx> = EvalStmtData<Rc<CapabilityLocals<'tcx>>>;

#[derive(Debug)]
pub struct PcgLocation<'tcx> {
    pub location: Location,
    pub states: DomainDataStates<Pcg<'tcx>>,
    pub(crate) actions: EvalStmtData<PcgActions<'tcx>>,
}

impl<'tcx> DebugLines<CompilerCtxt<'_, 'tcx>> for Vec<RepackOp<'tcx>> {
    fn debug_lines(&self, _repacker: CompilerCtxt<'_, 'tcx>) -> Vec<String> {
        self.iter().map(|r| format!("{r:?}")).collect()
    }
}

impl<'tcx> HasValidityCheck<'tcx> for PcgLocation<'tcx> {
    fn check_validity<C: Copy>(&self, repacker: CompilerCtxt<'_, 'tcx, C>) -> Result<(), String> {
        // TODO
        self.states.check_validity(repacker)
    }
}

impl<'tcx> PcgLocation<'tcx> {
    pub fn borrow_pcg_actions(&self, phase: EvalStmtPhase) -> BorrowPCGActions<'tcx> {
        self.actions[phase].borrow_pcg_actions()
    }
    pub fn actions(&self, phase: EvalStmtPhase) -> &PcgActions<'tcx> {
        &self.actions[phase]
    }

    pub fn ancestor_edges<'slf, 'mir: 'slf, 'bc: 'slf, C: Copy>(
        &'slf self,
        place: Place<'tcx>,
        repacker: CompilerCtxt<'mir, 'tcx, C>,
    ) -> FxHashSet<BorrowPCGEdgeRef<'tcx, 'slf>> {
        let borrows_graph = self.states[EvalStmtPhase::PostMain].borrow.graph();
        let mut ancestors = borrows_graph.ancestor_edges(place.into(), repacker);
        for rp in place.region_projections(repacker) {
            ancestors.extend(borrows_graph.ancestor_edges(rp.into(), repacker));
        }
        ancestors
    }

    pub fn aliases<'mir>(
        &self,
        place: impl Into<Place<'tcx>>,
        body: &'mir Body<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> FxHashSet<mir::Place<'tcx>> {
        let place: Place<'tcx> = place.into();
        // let place = place.with_inherent_region(ctxt);
        let ctxt = CompilerCtxt::new(body, tcx, ());
        self.states[EvalStmtPhase::PostMain]
            .borrow
            .graph()
            .aliases(place.into(), ctxt)
            .into_iter()
            .flat_map(|p| match p {
                PCGNode::Place(p) => p.as_current_place(),
                PCGNode::RegionProjection(p) => match p.base() {
                    MaybeRemoteRegionProjectionBase::Place(p) => {
                        let assoc_place = p.related_local_place();
                        if assoc_place.is_ref(ctxt) {
                            Some(assoc_place.project_deref(ctxt))
                        } else {
                            None
                        }
                    }
                    _ => None,
                },
            })
            .map(|p| p.to_rust_place(ctxt))
            .collect()
    }

    pub fn latest(&self) -> &Latest<'tcx> {
        &self.states[EvalStmtPhase::PostMain].borrow.latest
    }

    pub(crate) fn debug_lines(
        &self,
        phase: EvalStmtPhase,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> Vec<String> {
        let mut result = self.states[phase].debug_lines(repacker);
        for action in self.actions[phase].0.iter() {
            result.push(action.debug_line(repacker));
        }
        result
    }
}

#[derive(Debug)]
pub struct PcgTerminator<'tcx> {
    pub succs: Vec<PcgSuccessor<'tcx>>,
}
