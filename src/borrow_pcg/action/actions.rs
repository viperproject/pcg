use derive_more::{Deref, DerefMut};

use crate::borrow_pcg::action::BorrowPCGAction;
use crate::borrow_pcg::borrow_pcg_edge::BorrowPCGEdge;
use crate::borrow_pcg::edge::kind::BorrowPcgEdgeKind;
use crate::borrow_pcg::edge::outlives::BorrowFlowEdge;
use crate::borrow_pcg::graph::Conditioned;
use crate::borrow_pcg::unblock_graph::BorrowPCGUnblockAction;
use crate::rustc_interface::data_structures::fx::FxHashSet;
use crate::utils::json::ToJsonWithCompilerCtxt;
use crate::utils::CompilerCtxt;
use crate::{pcg_validity_assert, validity_checks_enabled, Weaken};

use super::BorrowPCGActionKind;

#[derive(Clone, Deref, DerefMut, Debug, Default)]
pub struct BorrowPCGActions<'tcx>(pub(crate) Vec<BorrowPCGAction<'tcx>>);

impl<'tcx> ToJsonWithCompilerCtxt<'tcx> for BorrowPCGActions<'tcx> {
    fn to_json(&self, repacker: CompilerCtxt<'_, 'tcx>) -> serde_json::Value {
        self.0
            .iter()
            .map(|a| a.to_json(repacker))
            .collect::<Vec<_>>()
            .into()
    }
}

impl<'tcx> BorrowPCGActions<'tcx> {
    /// Actions applied to the PCG, in the order they occurred.
    pub fn actions(&self) -> &[BorrowPCGAction<'tcx>] {
        &self.0
    }

    pub fn added_outlives_edges(&self) -> FxHashSet<Conditioned<BorrowFlowEdge<'tcx>>> {
        self.0
            .iter()
            .filter_map(|action| match action.kind() {
                BorrowPCGActionKind::AddEdge {
                    edge:
                        BorrowPCGEdge {
                            kind: BorrowPcgEdgeKind::BorrowFlow(edge),
                            conditions,
                            ..
                        },
                    ..
                } => Some(Conditioned::new(*edge, conditions.clone())),
                _ => None,
            })
            .collect()
    }

    pub fn weakens(&self) -> FxHashSet<Weaken<'tcx>> {
        self.0
            .iter()
            .filter_map(|action| match action.kind() {
                BorrowPCGActionKind::Weaken(weaken) => Some(*weaken),
                _ => None,
            })
            .collect()
    }

    pub fn unblock_actions(&self) -> Vec<BorrowPCGUnblockAction<'tcx>> {
        self.0
            .iter()
            .filter_map(|action| match action.kind() {
                BorrowPCGActionKind::RemoveEdge(edge) => Some(edge.clone().into()),
                _ => None,
            })
            .collect()
    }
}

impl<'tcx> BorrowPCGActions<'tcx> {
    pub(crate) fn new() -> Self {
        Self(vec![])
    }


    pub(crate) fn last(&self) -> Option<&BorrowPCGAction<'tcx>> {
        self.0.last()
    }

    pub(crate) fn push(&mut self, action: BorrowPCGAction<'tcx>, _ctxt: CompilerCtxt<'_, 'tcx>) {
        if validity_checks_enabled()
            && let Some(last) = self.last() {
                pcg_validity_assert!(last != &action, "Action {:?} to be pushed is the same as the last pushed action, this is probably a bug.", action);
            }
        self.0.push(action);
    }
}
