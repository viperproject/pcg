// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::action::PcgActions;

use crate::pcg::Pcg;
use crate::{
    pcg::{EvalStmtPhase, PcgError},
    utils::CompilerCtxt,
};

use super::triple::TripleWalker;

#[derive(Clone)]
pub struct FpcsEngine<'a, 'tcx> {
    pub(crate) repacker: CompilerCtxt<'a, 'tcx>,
}

impl<'a, 'tcx> FpcsEngine<'a, 'tcx> {
    pub(crate) fn analyze(
        &self,
        state: &mut Pcg<'tcx>,
        tw: &TripleWalker<'a, 'tcx>,
        phase: EvalStmtPhase,
    ) -> Result<PcgActions<'tcx>, PcgError> {
        let mut actions = PcgActions::default();
        match phase {
            EvalStmtPhase::PreOperands => {
                for triple in tw.operand_triples.iter() {
                    actions.extend(state.requires(triple.pre(), self.repacker)?);
                }
            }
            EvalStmtPhase::PostOperands => {
                for triple in tw.operand_triples.iter() {
                    state.owned_ensures(*triple);
                }
            }
            EvalStmtPhase::PreMain => {
                for triple in tw.main_triples.iter() {
                    actions.extend(state.requires(triple.pre(), self.repacker)?);
                }
            }
            EvalStmtPhase::PostMain => {
                for triple in tw.main_triples.iter() {
                    state.owned_ensures(*triple);
                }
            }
        }
        Ok(actions)
    }
}
