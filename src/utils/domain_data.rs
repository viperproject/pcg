use crate::borrows::engine::DataflowPhase;
use crate::rustc_interface::middle::mir::Location;

use super::eval_stmt_data::EvalStmtData;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DomainData<T> {
    pub(crate) entry_state: T,
    pub(crate) states: EvalStmtData<T>,
    phase: DataflowPhase,
}

impl<T: Default> Default for DomainData<T> {
    fn default() -> Self {
        Self {
            entry_state: T::default(),
            states: EvalStmtData::default(),
            phase: DataflowPhase::Init,
        }
    }
}

impl<T: Clone + Default> DomainData<T> {
    pub(crate) fn new(entry_state: T) -> Self {
        Self {
            entry_state,
            states: EvalStmtData::default(),
            phase: DataflowPhase::Init,
        }
    }
    pub(crate) fn pre_operands_complete(&mut self) {
        assert!(self.phase == DataflowPhase::Transfer);
        self.states.pre_operands = self.states.post_main.clone();
    }
    pub(crate) fn post_operands_complete(&mut self) {
        assert!(self.phase == DataflowPhase::Transfer);
        self.states.post_operands = self.states.post_main.clone();
    }

    pub(crate) fn pre_main_complete(&mut self) {
        assert!(self.phase == DataflowPhase::Transfer);
        self.states.pre_main = self.states.post_main.clone();
    }
    pub(crate) fn enter_location(&mut self, _location: Location) {
        if self.phase != DataflowPhase::Transfer {
            // The entry state may have taken into account previous joins
            self.states.post_main = self.entry_state.clone();
            self.phase = DataflowPhase::Transfer;
        } else {
            self.entry_state = self.states.post_main.clone();
        }
    }
    pub(crate) fn enter_join(&mut self) {
        if self.phase == DataflowPhase::Transfer {
            self.entry_state = self.states.post_main.clone();
            self.phase = DataflowPhase::Join;
        }
    }
}
