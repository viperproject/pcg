use serde_json::json;

use crate::rustc_interface::middle::mir::BasicBlock;
use crate::utils::json::ToJsonWithRepacker;
use crate::utils::PlaceRepacker;
use crate::DebugLines;
use crate::{borrow_pcg::action::BorrowPCGAction, free_pcs::RepackOp};

#[derive(Debug)]
pub struct PcgSuccessor<'tcx> {
    block: BasicBlock,
    owned_ops: Vec<RepackOp<'tcx>>,
    borrow_ops: Vec<BorrowPCGAction<'tcx>>,
}

impl<'tcx> PcgSuccessor<'tcx> {
    pub fn block(&self) -> BasicBlock {
        self.block
    }
    pub fn owned_ops(&self) -> &[RepackOp<'tcx>] {
        &self.owned_ops
    }
    pub fn borrow_ops(&self) -> &[BorrowPCGAction<'tcx>] {
        &self.borrow_ops
    }
    pub(crate) fn new(
        block: BasicBlock,
        owned_ops: Vec<RepackOp<'tcx>>,
        borrow_ops: Vec<BorrowPCGAction<'tcx>>,
    ) -> Self {
        Self {
            block,
            owned_ops,
            borrow_ops,
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
