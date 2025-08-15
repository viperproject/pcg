use derive_more::From;

use crate::pcg::EvalStmtPhase;

use super::arena::PcgArenaRef;
use super::eval_stmt_data::EvalStmtData;
use super::validity::HasValidityCheck;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct DomainData<T> {
    pub(crate) entry_state: T,
    pub(crate) states: DomainDataStates<T>,
}

impl<'a, T: Clone> DomainData<PcgArenaRef<'a, T>> {
    pub(crate) fn new(entry_state: PcgArenaRef<'a, T>) -> Self {
        Self {
            entry_state: entry_state.clone(),
            states: DomainDataStates::new(entry_state),
        }
    }
}

#[derive(From)]
pub enum DomainDataIndex {
    Eval(EvalStmtPhase),
    Initial,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DomainDataStates<T>(pub(crate) EvalStmtData<T>);

impl<'a, T: Clone> DomainDataStates<PcgArenaRef<'a, T>> {
    pub(crate) fn new(entry_state: PcgArenaRef<'a, T>) -> Self {
        Self(EvalStmtData::new(
            entry_state.clone(),
            entry_state.clone(),
            entry_state.clone(),
            entry_state,
        ))
    }
}

impl<T: Clone> DomainDataStates<PcgArenaRef<'_, T>> {
    pub(crate) fn to_owned(&self) -> DomainDataStates<T> {
        DomainDataStates(self.0.clone().map(|x| (*x).clone()))
    }
}
impl<'tcx, T: HasValidityCheck<'tcx>> HasValidityCheck<'tcx> for DomainDataStates<T> {
    fn check_validity(&self, ctxt: super::CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
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
