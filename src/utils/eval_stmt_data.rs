
use crate::pcg::EvalStmtPhase;
use crate::utils::json::ToJsonWithCompilerCtxt;
use crate::utils::validity::HasValidityCheck;
use crate::utils::CompilerCtxt;
use serde_json::json;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct EvalStmtData<T> {
    pub(crate) pre_operands: T,
    pub(crate) post_operands: T,
    pub(crate) pre_main: T,
    pub(crate) post_main: T,
}

impl<T> EvalStmtData<T> {
    pub(crate) fn new(pre_operands: T, post_operands: T, pre_main: T, post_main: T) -> Self {
        Self {
            pre_operands,
            post_operands,
            pre_main,
            post_main,
        }
    }
}

impl<'tcx, BC: Copy, T: ToJsonWithCompilerCtxt<'tcx, BC>> ToJsonWithCompilerCtxt<'tcx, BC> for EvalStmtData<T> {
    fn to_json(&self, ctxt: CompilerCtxt<'_, 'tcx, BC>) -> serde_json::Value {
        json!({
            "pre_operands": self.pre_operands.to_json(ctxt),
            "post_operands": self.post_operands.to_json(ctxt),
            "pre_main": self.pre_main.to_json(ctxt),
            "post_main": self.post_main.to_json(ctxt),
        })
    }
}

impl<T: Default> Default for EvalStmtData<T> {
    fn default() -> Self {
        Self {
            pre_operands: T::default(),
            post_operands: T::default(),
            pre_main: T::default(),
            post_main: T::default(),
        }
    }
}

impl<'tcx, T: HasValidityCheck<'tcx>> HasValidityCheck<'tcx> for EvalStmtData<T> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        // self.pre_operands.check_validity(ctxt)?;
        // self.post_operands.check_validity(ctxt)?;
        // self.pre_main.check_validity(ctxt)?;
        // Only check post main for now
        self.post_main.check_validity(ctxt)
    }
}
impl<T> EvalStmtData<T> {
    pub fn map<U>(self, f: impl Fn(T) -> U) -> EvalStmtData<U> {
        EvalStmtData {
            pre_operands: f(self.pre_operands),
            post_operands: f(self.post_operands),
            pre_main: f(self.pre_main),
            post_main: f(self.post_main),
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = (EvalStmtPhase, &T)> {
        [
            (EvalStmtPhase::PreOperands, &self.pre_operands),
            (EvalStmtPhase::PostOperands, &self.post_operands),
            (EvalStmtPhase::PreMain, &self.pre_main),
            (EvalStmtPhase::PostMain, &self.post_main),
        ]
        .into_iter()
    }

    #[allow(unused)]
    pub(crate) fn iter_mut(&mut self) -> impl Iterator<Item = (EvalStmtPhase, &mut T)> {
        [
            (EvalStmtPhase::PreOperands, &mut self.pre_operands),
            (EvalStmtPhase::PostOperands, &mut self.post_operands),
            (EvalStmtPhase::PreMain, &mut self.pre_main),
            (EvalStmtPhase::PostMain, &mut self.post_main),
        ]
        .into_iter()
    }

    pub(crate) fn get(&self, phase: EvalStmtPhase) -> &T {
        match phase {
            EvalStmtPhase::PreOperands => &self.pre_operands,
            EvalStmtPhase::PostOperands => &self.post_operands,
            EvalStmtPhase::PreMain => &self.pre_main,
            EvalStmtPhase::PostMain => &self.post_main,
        }
    }
    pub fn post_main(&self) -> &T {
        &self.post_main
    }
}

impl<T> std::ops::Index<EvalStmtPhase> for EvalStmtData<T> {
    type Output = T;

    fn index(&self, phase: EvalStmtPhase) -> &Self::Output {
        self.get(phase)
    }
}

impl<T> std::ops::IndexMut<EvalStmtPhase> for EvalStmtData<T> {
    fn index_mut(&mut self, phase: EvalStmtPhase) -> &mut Self::Output {
        match phase {
            EvalStmtPhase::PreOperands => &mut self.pre_operands,
            EvalStmtPhase::PostOperands => &mut self.post_operands,
            EvalStmtPhase::PreMain => &mut self.pre_main,
            EvalStmtPhase::PostMain => &mut self.post_main,
        }
    }
}
