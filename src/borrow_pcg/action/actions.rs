use derive_more::{Deref, DerefMut};

use crate::borrow_checker::BorrowCheckerInterface;
use crate::borrow_pcg::action::BorrowPcgAction;
use crate::borrow_pcg::borrow_pcg_edge::BorrowPcgEdge;
use crate::borrow_pcg::edge::kind::BorrowPcgEdgeKind;
use crate::borrow_pcg::edge::outlives::BorrowFlowEdge;
use crate::borrow_pcg::graph::Conditioned;
use crate::borrow_pcg::unblock_graph::BorrowPCGUnblockAction;
use crate::rustc_interface::data_structures::fx::FxHashSet;
use crate::utils::json::ToJsonWithCompilerCtxt;
use crate::utils::CompilerCtxt;
use crate::{pcg_validity_assert, validity_checks_enabled, Weaken};

use super::BorrowPcgActionKind;

#[derive(Clone, Deref, DerefMut, Debug, Default)]
pub struct BorrowPCGActions<'tcx>(pub(crate) Vec<BorrowPcgAction<'tcx>>);

impl<'tcx, 'a> ToJsonWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>
    for BorrowPCGActions<'tcx>
{
    fn to_json(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    ) -> serde_json::Value {
        self.0
            .iter()
            .map(|a| a.to_json(ctxt))
            .collect::<Vec<_>>()
            .into()
    }
}

impl<'tcx> BorrowPCGActions<'tcx> {
    /// Actions applied to the PCG, in the order they occurred.
    pub fn actions(&self) -> &[BorrowPcgAction<'tcx>] {
        &self.0
    }

    pub fn added_outlives_edges(&self) -> FxHashSet<Conditioned<BorrowFlowEdge<'tcx>>> {
        self.0
            .iter()
            .filter_map(|action| match action.kind() {
                BorrowPcgActionKind::AddEdge {
                    edge:
                        BorrowPcgEdge {
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
                BorrowPcgActionKind::Weaken(weaken) => Some(*weaken),
                _ => None,
            })
            .collect()
    }

    pub fn unblock_actions(&self) -> Vec<BorrowPCGUnblockAction<'tcx>> {
        self.0
            .iter()
            .filter_map(|action| match action.kind() {
                BorrowPcgActionKind::RemoveEdge(edge) => Some(edge.clone().into()),
                _ => None,
            })
            .collect()
    }
}

impl<'tcx> BorrowPCGActions<'tcx> {
    pub(crate) fn new() -> Self {
        Self(vec![])
    }

    pub(crate) fn last(&self) -> Option<&BorrowPcgAction<'tcx>> {
        self.0.last()
    }

    pub(crate) fn push(&mut self, action: BorrowPcgAction<'tcx>, _ctxt: CompilerCtxt<'_, 'tcx>) {
        if validity_checks_enabled()
            && let Some(last) = self.last()
        {
            pcg_validity_assert!(last != &action, "Action {:?} to be pushed is the same as the last pushed action, this is probably a bug.", action);
        }
        self.0.push(action);
    }
}
