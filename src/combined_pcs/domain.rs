// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use itertools::Itertools;
use std::{
    cell::RefCell,
    collections::BTreeMap,
    fmt::{Debug, Formatter, Result},
    rc::Rc,
};

use rustc_interface::{
    dataflow::fmt::DebugWithContext,
    dataflow::JoinSemiLattice,
    dataflow::{impls::MaybeLiveLocals, Results},
    middle::mir,
    middle::mir::BasicBlock,
};

use crate::{
    borrows::{
        borrow_pcg_edge::PCGNode,
        domain::{MaybeOldPlace, MaybeRemotePlace},
        engine::BorrowsDomain,
        unblock_graph::UnblockGraph,
    },
    free_pcs::{CapabilityLocal, FreePlaceCapabilitySummary},
    rustc_interface,
    visualization::generate_dot_graph,
    RECORD_PCS,
};

use super::{PcsContext, PcsEngine};

#[derive(Copy, Clone)]
pub struct DataflowIterationDebugInfo {
    pub join_with: BasicBlock,
}

#[derive(PartialEq, Eq, Copy, Clone, Debug, Ord, PartialOrd)]
pub enum DataflowStmtPhase {
    Initial,
    Join(BasicBlock),
    BeforeStart,
    BeforeAfter,
    Start,
    After,
}

impl DataflowStmtPhase {
    pub fn to_filename_str_part(&self) -> String {
        match self {
            DataflowStmtPhase::Join(block) => format!("join_{:?}", block),
            _ => format!("{:?}", self),
        }
    }
}

#[derive(Clone)]
pub struct PlaceCapabilitySummary<'a, 'tcx> {
    pub cgx: Rc<PcsContext<'a, 'tcx>>,
    pub block: Option<BasicBlock>,

    pub fpcs: FreePlaceCapabilitySummary<'a, 'tcx>,
    pub borrows: BorrowsDomain<'a, 'tcx>,
    dot_graphs: Option<Rc<RefCell<DotGraphs>>>,

    dot_output_dir: Option<String>,
}

/// Outermost Vec can be considered a map StatementIndex -> Vec<BTreeMap<DataflowStmtPhase, String>>
/// The inner Vec has one entry per iteration.
/// The BTreeMap maps each phase to a filename for the dot graph
#[derive(Clone)]
pub struct DotGraphs(Vec<Vec<BTreeMap<DataflowStmtPhase, String>>>);

impl DotGraphs {
    pub fn new() -> Self {
        Self(vec![])
    }

    fn relative_filename(
        &self,
        phase: DataflowStmtPhase,
        block: BasicBlock,
        statement_index: usize,
    ) -> String {
        let iteration = self.num_iterations(statement_index);
        format!(
            "{:?}_stmt_{}_iteration_{}_{}.dot",
            block,
            statement_index,
            iteration,
            phase.to_filename_str_part()
        )
    }

    pub fn register_new_iteration(&mut self, statement_index: usize) {
        if self.0.len() <= statement_index {
            self.0.resize_with(statement_index + 1, Vec::new);
        }
        self.0[statement_index].push(BTreeMap::new());
    }

    pub fn num_iterations(&self, statement_index: usize) -> usize {
        self.0[statement_index].len()
    }

    pub fn insert(
        &mut self,
        statement_index: usize,
        phase: DataflowStmtPhase,
        filename: String,
    ) -> bool {
        let top = self.0[statement_index].last_mut().unwrap();
        top.insert(phase, filename).is_none()
    }

    pub fn write_json_file(&self, filename: &str) {
        let iterations_json = self
            .0
            .iter()
            .map(|iterations| {
                iterations
                    .into_iter()
                    .map(|map| {
                        map.into_iter()
                            .sorted_by_key(|x| x.0)
                            .map(|(phase, filename)| (format!("{:?}", phase), filename))
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        std::fs::write(
            filename,
            serde_json::to_string_pretty(&iterations_json).unwrap(),
        )
        .unwrap();
    }
}

impl<'a, 'tcx> PlaceCapabilitySummary<'a, 'tcx> {
    pub(crate) fn is_valid(&self) -> bool {
        self.borrows.is_valid()
    }

    pub fn is_initialized(&self) -> bool {
        self.block.is_some()
    }

    pub fn set_block(&mut self, block: BasicBlock) {
        self.block = Some(block);
        self.borrows.set_block(block);
    }

    pub fn set_dot_graphs(&mut self, dot_graphs: Rc<RefCell<DotGraphs>>) {
        self.dot_graphs = Some(dot_graphs);
    }

    pub fn block(&self) -> BasicBlock {
        self.block.unwrap()
    }

    pub fn dot_graphs(&self) -> Rc<RefCell<DotGraphs>> {
        self.dot_graphs.clone().unwrap()
    }

    fn dot_filename_for(
        &self,
        output_dir: &str,
        phase: DataflowStmtPhase,
        statement_index: usize,
    ) -> String {
        format!(
            "{}/{}",
            output_dir,
            self.dot_graphs()
                .borrow()
                .relative_filename(phase, self.block(), statement_index)
        )
    }
    pub fn generate_dot_graph(&mut self, phase: DataflowStmtPhase, statement_index: usize) {
        if !*RECORD_PCS.lock().unwrap() {
            return;
        }
        if self.block().as_usize() == 0 {
            assert!(!matches!(phase, DataflowStmtPhase::Join(_)));
        }
        if let Some(output_dir) = &self.dot_output_dir {
            if phase == DataflowStmtPhase::Initial {
                self.dot_graphs()
                    .borrow_mut()
                    .register_new_iteration(statement_index);
            }
            let relative_filename =
                self.dot_graphs()
                    .borrow()
                    .relative_filename(phase, self.block(), statement_index);
            let filename = self.dot_filename_for(&output_dir, phase, statement_index);
            assert!(self.dot_graphs().borrow_mut().insert(
                statement_index,
                phase,
                relative_filename
            ));

            let (fpcs, borrows) = match phase {
                DataflowStmtPhase::Initial | DataflowStmtPhase::BeforeStart => {
                    (&self.fpcs.pre_operands, &self.borrows.states.before_start)
                }
                DataflowStmtPhase::BeforeAfter => {
                    (&self.fpcs.post_operands, &self.borrows.states.before_after)
                }
                DataflowStmtPhase::Start => (&self.fpcs.pre_main, &self.borrows.states.start),
                DataflowStmtPhase::After | DataflowStmtPhase::Join(_) => {
                    (&self.fpcs.post_main, self.borrows.after_state())
                }
            };

            generate_dot_graph(self.cgx.rp, fpcs, borrows, &filename).unwrap();
        }
    }

    pub fn new(
        cgx: Rc<PcsContext<'a, 'tcx>>,
        block: Option<BasicBlock>,
        dot_output_dir: Option<String>,
        dot_graphs: Option<Rc<RefCell<DotGraphs>>>,
        maybe_live_locals: Rc<Results<'tcx, MaybeLiveLocals>>,
    ) -> Self {
        let fpcs = FreePlaceCapabilitySummary::new(cgx.rp);
        let borrows = BorrowsDomain::new(
            cgx.rp,
            cgx.mir.output_facts.clone().unwrap(),
            cgx.mir.location_table.clone().unwrap(),
            block,
            maybe_live_locals.clone(),
        );
        Self {
            cgx,
            block,
            fpcs,
            borrows,
            dot_graphs,
            dot_output_dir,
        }
    }
}

impl Eq for PlaceCapabilitySummary<'_, '_> {}
impl PartialEq for PlaceCapabilitySummary<'_, '_> {
    fn eq(&self, other: &Self) -> bool {
        self.fpcs == other.fpcs && self.borrows == other.borrows
    }
}
impl Debug for PlaceCapabilitySummary<'_, '_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{:?}\n{:?}", self.fpcs, self.borrows)
    }
}

impl JoinSemiLattice for PlaceCapabilitySummary<'_, '_> {
    fn join(&mut self, other: &Self) -> bool {
        if !other.is_valid() {
            eprintln!(
                "Block {:?} is invalid. Body source: {:?}",
                other.block(),
                self.cgx.mir.body.source
            );
        }
        debug_assert!(other.is_valid(), "Block {:?} is invalid", other.block());
        assert!(self.is_initialized() && other.is_initialized());
        if self.block().as_usize() == 0 {
            panic!("{:?}", other.block());
        }
        let fpcs = self.fpcs.join(&other.fpcs);
        let borrows = self.borrows.join(&other.borrows);
        let mut g = UnblockGraph::new();
        for root in self.borrows.states.after.roots(self.cgx.rp) {
            if let PCGNode::Place(MaybeRemotePlace::Local(MaybeOldPlace::Current { place: root })) =
                root
            {
                match &self.fpcs.post_main[root.local] {
                    CapabilityLocal::Unallocated => {
                        g.unblock_node(root.into(), &self.borrows.after_state(), self.cgx.rp);
                    }
                    CapabilityLocal::Allocated(projs) => {
                        if !(*projs).contains_key(&root) {
                            g.unblock_node(root.into(), &self.borrows.after_state(), self.cgx.rp);
                        }
                    }
                }
            }
        }
        let ub = self.borrows.states.after.apply_unblock_graph(
            g,
            self.cgx.rp,
            mir::Location {
                block: self.block(),
                statement_index: 0,
            },
        );
        self.dot_graphs().borrow_mut().register_new_iteration(0);
        self.generate_dot_graph(DataflowStmtPhase::Join(other.block()), 0);
        fpcs || borrows || ub
    }
}

impl<'a, 'tcx> DebugWithContext<PcsEngine<'a, 'tcx>> for PlaceCapabilitySummary<'a, 'tcx> {
    fn fmt_diff_with(
        &self,
        old: &Self,
        ctxt: &PcsEngine<'a, 'tcx>,
        f: &mut Formatter<'_>,
    ) -> Result {
        self.fpcs.fmt_diff_with(&old.fpcs, &ctxt.fpcs, f)
    }
}
