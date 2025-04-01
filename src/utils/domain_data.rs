use std::rc::Rc;


use crate::borrow_pcg::engine::DataflowPhase;
use crate::pcg::EvalStmtPhase;

use super::eval_stmt_data::EvalStmtData;
use super::incoming_states::IncomingStates;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct DomainData<T> {
    pub(crate) entry_state: Rc<T>,
    pub(crate) incoming_states: IncomingStates,
    pub(crate) states: DomainDataStates<T>,
    phase: DataflowPhase,
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
    pub(crate) fn get_mut(&mut self, phase: EvalStmtPhase) -> &mut T {
        Rc::<T>::make_mut(&mut self.0[phase])
    }
}

impl<T: Default> Default for DomainData<T> {
    fn default() -> Self {
        Self {
            entry_state: Rc::new(Default::default()),
            incoming_states: Default::default(),
            states: Default::default(),
            phase: DataflowPhase::Init,
        }
    }
}

impl<T: Clone> DomainData<Option<T>> {
    pub(crate) fn unwrap_mut(&mut self, phase: EvalStmtPhase) -> &mut T {
        self.states.get_mut(phase).as_mut().unwrap()
    }

    pub(crate) fn unwrap(&self, phase: EvalStmtPhase) -> &T {
        self.states[phase].as_ref().as_ref().unwrap()
    }
}

impl<T: Clone> DomainData<T> {
    pub(crate) fn enter_transfer_fn(&mut self) {
        if self.phase != DataflowPhase::Transfer {
            // The entry state may have taken into account previous joins
            self.states.0.post_main = self.entry_state.clone();
            self.set_phase(DataflowPhase::Transfer);
        } else {
            self.entry_state = self.states.0.post_main.clone();
        }
    }
}

impl<T> DomainData<T> {
    pub(crate) fn set_phase(&mut self, phase: DataflowPhase) {
        assert!(phase != DataflowPhase::Init);
        self.phase = phase;
    }
    pub(crate) fn enter_join(&mut self) {
        if self.phase == DataflowPhase::Transfer {
            self.entry_state = self.states.0.post_main.clone();
            self.phase = DataflowPhase::Join;
        }
    }
}
