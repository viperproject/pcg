use std::rc::Rc;

use serde_json::json;

use crate::borrow_pcg::action::actions::BorrowPCGActions;
use crate::borrow_pcg::graph::BorrowsGraph;
use crate::borrow_pcg::latest::Latest;
use crate::borrow_pcg::state::BorrowsState;
use crate::free_pcs::RepackOp;
use crate::rustc_interface::middle::mir::BasicBlock;
use crate::utils::json::ToJsonWithRepacker;
use crate::utils::PlaceRepacker;
use crate::DebugLines;

#[derive(Debug)]
pub struct PcgSuccessor<'tcx> {
    block: BasicBlock,
    owned_ops: Vec<RepackOp<'tcx>>,
    borrow_ops: BorrowPCGActions<'tcx>,
    entry_state: Rc<BorrowsState<'tcx>>,
}

impl<'tcx> PcgSuccessor<'tcx> {
    pub fn block(&self) -> BasicBlock {
        self.block
    }
    pub fn owned_ops(&self) -> &[RepackOp<'tcx>] {
        &self.owned_ops
    }
    pub fn borrow_ops(&self) -> &BorrowPCGActions<'tcx> {
        &self.borrow_ops
    }
    pub fn latest(&self) -> &Latest<'tcx> {
        &self.entry_state.latest
    }
    pub fn entry_graph(&self) -> &BorrowsGraph<'tcx> {
        self.entry_state.graph()
    }
    pub(crate) fn new(
        block: BasicBlock,
        owned_ops: Vec<RepackOp<'tcx>>,
        borrow_ops: BorrowPCGActions<'tcx>,
        entry_state: Rc<BorrowsState<'tcx>>,
    ) -> Self {
        Self {
            block,
            owned_ops,
            borrow_ops,
            entry_state,
        }
    }
}

impl<'tcx> ToJsonWithRepacker<'tcx> for PcgSuccessor<'tcx> {
    fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        json!({
            "block": self.block().index(),
            "owned_ops": self.owned_ops().iter().map(|r| r.to_json()).collect::<Vec<_>>(),
            "borrow_ops": self.borrow_ops().iter().map(|a| a.to_json(repacker)).collect::<Vec<_>>(),
        })
    }
}

impl<'tcx> DebugLines<PlaceRepacker<'_, 'tcx>> for PcgSuccessor<'tcx> {
    fn debug_lines(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Vec<String> {
        let mut result = Vec::new();
        result.push(format!("Block: {}", self.block().index()));
        result.extend(self.owned_ops().iter().map(|r| format!("{:?}", r)));
        result.extend(self.borrow_ops().iter().map(|a| a.debug_line(repacker)));
        result
    }
}
