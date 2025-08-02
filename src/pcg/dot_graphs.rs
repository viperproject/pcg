use std::collections::BTreeMap;

use serde_derive::Serialize;

use crate::RECORD_PCG;
use crate::pcg::{DataflowStmtPhase, EvalStmtPhase, PcgDebugData, PcgRef};
use crate::rustc_interface::middle::mir::{self, BasicBlock};
use crate::utils::CompilerCtxt;
use crate::visualization::write_pcg_dot_graph_to_file;

#[derive(Clone, Serialize, Default)]
pub(crate) struct PcgDotGraphsForBlock(Vec<PcgDotGraphsForStmt>);

#[derive(Clone, Serialize, Default)]
pub(crate) struct PcgDotGraphsForIteration {
    at_phase: Vec<(DataflowStmtPhase, String)>,
    actions: BTreeMap<EvalStmtPhase, Vec<String>>,
}

#[derive(Clone, Serialize, Default)]
struct PcgDotGraphsForStmt {
    iterations: Vec<PcgDotGraphsForIteration>,
}

impl PcgDotGraphsForStmt {
    fn num_iterations(&self) -> usize {
        self.iterations.len()
    }
}

impl PcgDotGraphsForBlock {
    pub(crate) fn relative_filename(
        &self,
        block: BasicBlock,
        statement_index: usize,
        to_graph: ToGraph,
    ) -> String {
        let iteration = self.num_iterations(statement_index);
        match to_graph {
            ToGraph::Phase(phase) => {
                format!(
                    "{:?}_stmt_{}_iteration_{}_{}.dot",
                    block,
                    statement_index,
                    iteration,
                    phase.to_filename_str_part()
                )
            }
            ToGraph::Action(phase, action_idx) => {
                format!(
                    "{:?}_stmt_{}_iteration_{}_{:?}_action_{}.dot",
                    block, statement_index, iteration, phase, action_idx,
                )
            }
        }
    }

    pub(crate) fn num_iterations(&self, statement_index: usize) -> usize {
        if self.0.len() <= statement_index {
            0
        } else {
            self.0[statement_index].num_iterations()
        }
    }

    fn last_iteration_mut(&mut self, statement_index: usize) -> &mut PcgDotGraphsForIteration {
        if self.0.len() <= statement_index {
            tracing::error!("Statement index out of bounds: {}", statement_index);
        }
        self.0[statement_index].iterations.last_mut().unwrap()
    }

    pub(crate) fn register_new_iteration(
        &mut self,
        statement_index: usize,
    ) -> &mut PcgDotGraphsForIteration {
        tracing::debug!(
            "Registering new iteration for statement {}",
            statement_index
        );
        if self.0.len() <= statement_index {
            self.0
                .resize_with(statement_index + 1, PcgDotGraphsForStmt::default);
        }
        self.0[statement_index]
            .iterations
            .push(PcgDotGraphsForIteration::default());
        self.last_iteration_mut(statement_index)
    }

    pub(crate) fn insert_for_phase(
        &mut self,
        statement_index: usize,
        phase: DataflowStmtPhase,
        filename: String,
    ) {
        self.last_iteration_mut(statement_index)
            .at_phase
            .push((phase, filename));
    }

    pub(crate) fn insert_for_action(
        &mut self,
        statement_index: usize,
        phase: EvalStmtPhase,
        action_idx: usize,
        filename: String,
    ) {
        let top = self.last_iteration_mut(statement_index);
        let within_phase = top.actions.entry(phase).or_default();
        assert_eq!(within_phase.len(), action_idx);
        within_phase.push(filename);
    }

    pub(crate) fn write_json_file(&self, filename: &str) {
        std::fs::write(filename, serde_json::to_string_pretty(&self.0).unwrap()).unwrap();
    }
}

fn dot_filename_for(output_dir: &str, relative_filename: &str) -> String {
    format!("{}/{}", output_dir, relative_filename)
}

#[derive(Clone, Copy)]
pub(crate) enum ToGraph {
    Phase(DataflowStmtPhase),
    Action(EvalStmtPhase, usize),
}

pub(crate) fn generate_dot_graph<'tcx>(
    block: BasicBlock,
    statement_index: usize,
    to_graph: ToGraph,
    pcg: PcgRef<'_, 'tcx>,
    debug_data: Option<&PcgDebugData>,
    ctxt: CompilerCtxt<'_, 'tcx>,
) {
    if !*RECORD_PCG.lock().unwrap() {
        return;
    }
    if block.as_usize() == 0 {
        assert!(!matches!(
            to_graph,
            ToGraph::Phase(DataflowStmtPhase::Join(_))
        ));
    }
    if let Some(debug_data) = debug_data {
        let relative_filename =
            debug_data
                .dot_graphs
                .borrow()
                .relative_filename(block, statement_index, to_graph);
        let filename = dot_filename_for(&debug_data.dot_output_dir, &relative_filename);
        match to_graph {
            ToGraph::Action(phase, action_idx) => {
                debug_data.dot_graphs.borrow_mut().insert_for_action(
                    statement_index,
                    phase,
                    action_idx,
                    relative_filename,
                );
            }
            ToGraph::Phase(phase) => debug_data.dot_graphs.borrow_mut().insert_for_phase(
                statement_index,
                phase,
                relative_filename,
            ),
        }

        write_pcg_dot_graph_to_file(
            pcg,
            ctxt,
            mir::Location {
                block,
                statement_index,
            },
            &filename,
        )
        .unwrap();
    }
}
