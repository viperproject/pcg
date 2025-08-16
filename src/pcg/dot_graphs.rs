use crate::pcg::{DataflowStmtPhase, EvalStmtPhase};
use crate::pcg_validity_assert;
use crate::rustc_interface::middle::mir::{self, BasicBlock};
use crate::utils::{CompilerCtxt, StmtGraphs};

#[derive(Clone, Debug)]
pub(crate) struct PcgDotGraphsForBlock {
    graphs: Vec<StmtGraphs>,
    block: BasicBlock,
}

impl PcgDotGraphsForBlock {
    pub(crate) fn new(block: BasicBlock, ctxt: CompilerCtxt<'_, '_>) -> Self {
        let num_statements = ctxt.body().basic_blocks[block].statements.len();
        Self {
            block,
            graphs: vec![StmtGraphs::default(); num_statements + 1],
        }
    }

    pub(crate) fn write_json_file(&self, filename: &str) {
        std::fs::write(
            filename,
            serde_json::to_string_pretty(&self.graphs).unwrap(),
        )
        .unwrap();
    }

    pub(crate) fn insert_for_action(
        &mut self,
        location: mir::Location,
        phase: EvalStmtPhase,
        action_idx: usize,
        filename: String,
    ) {
        pcg_validity_assert!(location.block == self.block);
        tracing::info!(
            "Inserting for action at block {:?}, statement index {}, action_idx {}",
            self.block,
            location.statement_index,
            action_idx
        );
        self.graphs[location.statement_index].insert_for_action(phase, action_idx, filename);
    }

    pub(crate) fn insert_for_phase(
        &mut self,
        statement_index: usize,
        phase: DataflowStmtPhase,
        filename: String,
    ) {
        self.graphs[statement_index].insert_for_phase(phase, filename);
    }
}
