// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::free_pcs::RepackOp;

use crate::{
    borrow_pcg::state::BorrowsState,
    combined_pcs::{EvalStmtPhase, PcgError},
    utils::PlaceRepacker,
};

use super::CapabilityLocals;
use super::triple::TripleWalker;

#[derive(Clone)]
pub struct FpcsEngine<'a, 'tcx> {
    pub(crate) repacker: PlaceRepacker<'a, 'tcx>,
}

impl<'a, 'tcx> FpcsEngine<'a, 'tcx> {
    pub(crate) fn analyze(
        &self,
        state: &mut CapabilityLocals<'tcx>,
        tw: &TripleWalker<'a, 'tcx>,
        borrows: &BorrowsState<'tcx>,
        phase: EvalStmtPhase,
    ) -> Result<Vec<RepackOp<'tcx>>, PcgError> {
        let mut actions = vec![];
        match phase {
            EvalStmtPhase::PreOperands => {
                for triple in tw.operand_triples.iter() {
                    actions.extend(state.requires(triple.pre(), self.repacker, borrows)?);
                }
            }
            EvalStmtPhase::PostOperands => {
                for triple in tw.operand_triples.iter() {
                    let triple = triple.replace_place(self.repacker);
                    state.ensures(triple, self.repacker);
                }
            }
            EvalStmtPhase::PreMain => {
                for triple in tw.main_triples.iter() {
                    actions.extend(state.requires(triple.pre(), self.repacker, borrows)?);
                }
            }
            EvalStmtPhase::PostMain => {
                for triple in tw.main_triples.iter() {
                    state.ensures(*triple, self.repacker);
                }
            }
        }
        Ok(actions)
    }
}
