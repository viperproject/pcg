use std::rc::Rc;

use serde_json::json;

use crate::action::PcgActions;
use crate::borrow_checker::BorrowCheckerInterface;
use crate::borrow_pcg::graph::BorrowsGraph;
use crate::borrow_pcg::state::BorrowsState;
use crate::rustc_interface::middle::mir::BasicBlock;
use crate::utils::json::ToJsonWithCompilerCtxt;
use crate::utils::CompilerCtxt;
use crate::DebugLines;

#[derive(Debug)]
pub struct PcgSuccessor<'tcx> {
    block: BasicBlock,
    pub(crate) actions: PcgActions<'tcx>,
    entry_state: Rc<BorrowsState<'tcx>>,
}

impl<'tcx> PcgSuccessor<'tcx> {
    pub fn actions(&self) -> &PcgActions<'tcx> {
        &self.actions
    }
    pub fn block(&self) -> BasicBlock {
        self.block
    }
    pub fn entry_graph(&self) -> &BorrowsGraph<'tcx> {
        self.entry_state.graph()
    }
    pub(crate) fn new(
        block: BasicBlock,
        actions: PcgActions<'tcx>,
        entry_state: Rc<BorrowsState<'tcx>>,
    ) -> Self {
        Self {
            block,
            actions,
            entry_state,
        }
    }
}

impl<'tcx, 'a> ToJsonWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>
    for PcgSuccessor<'tcx>
{
    fn to_json(&self, repacker: CompilerCtxt<'_, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>>) -> serde_json::Value {
        json!({
            "block": self.block().index(),
            "actions": self.actions.to_json(repacker),
        })
    }
}

impl<'tcx> DebugLines<CompilerCtxt<'_, 'tcx>> for PcgSuccessor<'tcx> {
    fn debug_lines(&self, repacker: CompilerCtxt<'_, 'tcx>) -> Vec<String> {
        let mut result = Vec::new();
        result.push(format!("Block: {}", self.block().index()));
        result.extend(self.actions.iter().map(|a| a.debug_line(repacker)));
        result
    }
}
