use derive_more::TryInto;
use serde::{Serialize, Serializer};

use crate::pcg::EvalStmtPhase;
use crate::rustc_interface::middle::mir::BasicBlock;

#[derive(PartialEq, Eq, Copy, Clone, Debug, Ord, PartialOrd, TryInto)]
pub enum DataflowStmtPhase {
    Initial,
    EvalStmt(EvalStmtPhase),
    Join(BasicBlock),
}

impl From<EvalStmtPhase> for DataflowStmtPhase {
    fn from(phase: EvalStmtPhase) -> Self {
        DataflowStmtPhase::EvalStmt(phase)
    }
}

impl std::fmt::Display for DataflowStmtPhase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DataflowStmtPhase::Initial => write!(f, "initial"),
            DataflowStmtPhase::EvalStmt(phase) => write!(f, "{phase}"),
            DataflowStmtPhase::Join(block) => write!(f, "join {block:?}"),
        }
    }
}
impl DataflowStmtPhase {
    pub(crate) fn to_filename_str_part(self) -> String {
        self.to_string()
    }
}

impl Serialize for DataflowStmtPhase {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&self.to_filename_str_part())
    }
}
