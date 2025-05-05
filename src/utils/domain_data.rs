use std::alloc::Allocator;
use std::rc::Rc;

use derive_more::From;

use crate::pcg::EvalStmtPhase;

use super::arena::ArenaRef;
use super::eval_stmt_data::EvalStmtData;
use super::incoming_states::IncomingStates;
use super::validity::HasValidityCheck;

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub(crate) struct DomainData<T> {
    pub(crate) entry_state: T,
    pub(crate) incoming_states: IncomingStates,
    pub(crate) states: DomainDataStates<T>,
}

impl<T: Clone> DomainData<T> {
    pub(crate) fn new(entry_state: T) -> Self {
        Self {
            entry_state: entry_state.clone(),
            incoming_states: IncomingStates::default(),
            states: DomainDataStates::new(entry_state),
        }
    }
}

#[derive(From)]
pub enum DomainDataIndex {
    Eval(EvalStmtPhase),
    Initial,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct DomainDataStates<T>(pub(crate) EvalStmtData<T>);

impl<T: Clone> DomainDataStates<T> {
    pub(crate) fn new(entry_state: T) -> Self {
        Self(EvalStmtData::new(
            entry_state.clone(),
            entry_state.clone(),
            entry_state.clone(),
            entry_state,
        ))
    }
}

impl<T: Clone, A: Allocator + Clone> DomainDataStates<ArenaRef<T, A>> {
    pub(crate) fn to_owned(&self) -> DomainDataStates<T> {
        DomainDataStates(self.0.clone().map(|x| (*x).clone()))
    }
}
impl<'tcx, T: HasValidityCheck<'tcx>> HasValidityCheck<'tcx> for DomainDataStates<T> {
    fn check_validity<C: Copy>(
        &self,
        ctxt: super::CompilerCtxt<'_, 'tcx, C>,
    ) -> Result<(), String> {
        self.0.check_validity(ctxt)
    }
}

impl<T> std::ops::Index<EvalStmtPhase> for DomainDataStates<T> {
    type Output = T;

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
    type Output = T;

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
