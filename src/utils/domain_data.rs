use std::rc::Rc;


use derive_more::From;

use crate::pcg::EvalStmtPhase;

use super::eval_stmt_data::EvalStmtData;
use super::incoming_states::IncomingStates;
use super::validity::HasValidityCheck;

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub(crate) struct DomainData<T> {
    pub(crate) entry_state: Rc<T>,
    pub(crate) incoming_states: IncomingStates,
    pub(crate) states: DomainDataStates<T>,
}

#[derive(From)]
pub enum DomainDataIndex {
    Eval(EvalStmtPhase),
    Initial,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct DomainDataStates<T>(pub(crate) EvalStmtData<Rc<T>>);

impl<'tcx, T: HasValidityCheck<'tcx>> HasValidityCheck<'tcx> for DomainDataStates<T> {
    fn check_validity<C: Copy>(&self, repacker: super::CompilerCtxt<'_, 'tcx, '_, C>) -> Result<(), String> {
        self.0.check_validity(repacker)
    }
}

impl<T> std::ops::Index<EvalStmtPhase> for DomainDataStates<T> {
    type Output = Rc<T>;

    fn index(&self, phase: EvalStmtPhase) -> &Self::Output {
        &self.0[phase]
    }
}

impl<T> std::ops::IndexMut<EvalStmtPhase> for DomainDataStates<T> {
    fn index_mut(&mut self, phase: EvalStmtPhase) -> &mut Self::Output {
        &mut self.0[phase]
    }
}

impl<T> std::ops::Index<DomainDataIndex> for DomainData<T> {
    type Output = Rc<T>;

    fn index(&self, phase: DomainDataIndex) -> &Self::Output {
        match phase {
            DomainDataIndex::Eval(phase) => &self.states[phase],
            DomainDataIndex::Initial => &self.entry_state,
        }
    }
}

impl<T> std::ops::IndexMut<DomainDataIndex> for DomainData<T> {
    fn index_mut(&mut self, phase: DomainDataIndex) -> &mut Self::Output {
        match phase {
            DomainDataIndex::Eval(phase) => &mut self.states[phase],
            DomainDataIndex::Initial => &mut self.entry_state,
        }
    }
}
