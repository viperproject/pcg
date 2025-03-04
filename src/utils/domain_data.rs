use std::rc::Rc;

use crate::borrow_pcg::engine::DataflowPhase;
use crate::combined_pcs::EvalStmtPhase;
use crate::rustc_interface::middle::mir::Location;

use super::eval_stmt_data::EvalStmtData;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DomainData<T> {
    pub(crate) entry_state: Rc<T>,
    pub(crate) states: DomainDataStates<T>,
    pub(crate) phase: DataflowPhase,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct DomainDataStates<T>(pub(crate) EvalStmtData<Rc<T>>);

impl<T> std::ops::Index<EvalStmtPhase> for DomainDataStates<T> {
    type Output = Rc<T>;

    fn index(&self, phase: EvalStmtPhase) -> &Self::Output {
        &self.0[phase]
    }
}

impl<T: Clone> DomainDataStates<T> {
    pub fn new(entry_state: Rc<T>) -> Self {
        Self(EvalStmtData {
            pre_operands: entry_state.clone(),
            post_operands: entry_state.clone(),
            pre_main: entry_state.clone(),
            post_main: entry_state,
        })
    }
    pub(crate) fn get_mut(&mut self, phase: EvalStmtPhase) -> &mut T {
        Rc::<T>::make_mut(&mut self.0[phase])
    }
}

impl<T: Default> Default for DomainData<T> {
    fn default() -> Self {
        Self {
            entry_state: Rc::default(),
            states: Default::default(),
            phase: DataflowPhase::Init,
        }
    }
}
impl <T: Clone> DomainData<T> {
    pub(crate) fn new(entry_state: Rc<T>) -> Self {
        Self {
            entry_state: entry_state.clone(),
            states: DomainDataStates::new(entry_state),
            phase: DataflowPhase::Init,
        }
    }
}

impl<T: Clone> DomainData<T> {
    pub(crate) fn get_mut(&mut self, phase: EvalStmtPhase) -> &mut T {
        self.states.get_mut(phase)
    }
    pub(crate) fn pre_operands_complete(&mut self) {
        assert!(self.phase == DataflowPhase::Transfer);
        self.states.0.pre_operands = self.states.0.post_main.clone();
    }
    pub(crate) fn post_operands_complete(&mut self) {
        assert!(self.phase == DataflowPhase::Transfer);
        self.states.0.post_operands = self.states.0.post_main.clone();
    }

    pub(crate) fn pre_main_complete(&mut self) {
        assert!(self.phase == DataflowPhase::Transfer);
        self.states.0.pre_main = self.states.0.post_main.clone();
    }
    pub(crate) fn enter_location(&mut self, _location: Location) {
        if self.phase != DataflowPhase::Transfer {
            // The entry state may have taken into account previous joins
            self.states.0.post_main = self.entry_state.clone();
            self.phase = DataflowPhase::Transfer;
        } else {
            self.entry_state = self.states.0.post_main.clone();
        }
    }
    pub(crate) fn enter_join(&mut self) {
        if self.phase == DataflowPhase::Transfer {
            self.entry_state = self.states.0.post_main.clone();
            self.phase = DataflowPhase::Join;
        }
    }
}
