use derive_more::{Deref, DerefMut, From};

use crate::{
    borrow_pcg::{
        action::{actions::BorrowPCGActions, BorrowPCGAction, BorrowPCGActionKind},
        unblock_graph::BorrowPCGUnblockAction,
    },
    free_pcs::RepackOp,
    utils::{json::ToJsonWithCompilerCtxt, CompilerCtxt},
};

#[derive(Clone, PartialEq, Eq, Debug, From, Default, Deref, DerefMut)]
pub struct PcgActions<'tcx>(pub(crate) Vec<PcgAction<'tcx>>);

impl<'tcx> ToJsonWithCompilerCtxt<'tcx> for PcgActions<'tcx> {
    fn to_json(&self, repacker: CompilerCtxt<'_, 'tcx>) -> serde_json::Value {
        self.0.iter().map(|a| a.to_json(repacker)).collect()
    }
}

impl<'tcx> From<BorrowPCGActions<'tcx>> for PcgActions<'tcx> {
    fn from(actions: BorrowPCGActions<'tcx>) -> Self {
       PcgActions(actions.0.into_iter().map(|a| a.into()).collect::<Vec<_>>())
    }
}

impl<'tcx> From<Vec<RepackOp<'tcx>>> for PcgActions<'tcx> {
    fn from(actions: Vec<RepackOp<'tcx>>) -> Self {
        PcgActions(actions.into_iter().map(|a| a.into()).collect::<Vec<_>>())
    }
}

impl<'tcx> PcgActions<'tcx> {
    pub fn borrow_pcg_actions(&self) -> BorrowPCGActions<'tcx> {
        BorrowPCGActions(
            self.0
                .iter()
                .filter_map(|action| match action {
                    PcgAction::Borrow(action) => Some(action.clone()),
                    _ => None,
                })
                .collect(),
        )
    }

    pub fn iter(&self) -> impl Iterator<Item = &PcgAction<'tcx>> {
        self.0.iter()
    }

    pub fn owned_pcg_actions(&self) -> Vec<&RepackOp<'tcx>> {
        self.0
            .iter()
            .filter_map(|action| match action {
                PcgAction::Owned(action) => Some(action),
                _ => None,
            })
            .collect()
    }

    pub fn borrow_pcg_unblock_actions(&self) -> Vec<BorrowPCGUnblockAction<'tcx>> {
        self.0
            .iter()
            .filter_map(|action| match action {
                PcgAction::Borrow(BorrowPCGAction {
                    kind: BorrowPCGActionKind::RemoveEdge(edge),
                    ..
                }) => Some(edge.clone().into()),
                _ => None,
            })
            .collect()
    }
}

#[derive(Clone, PartialEq, Eq, Debug, From)]
pub enum PcgAction<'tcx> {
    Borrow(BorrowPCGAction<'tcx>),
    Owned(RepackOp<'tcx>),
}

impl<'tcx> PcgAction<'tcx> {
    pub(crate) fn debug_line(&self, repacker: CompilerCtxt<'_, 'tcx>) -> String {
        match self {
            PcgAction::Borrow(action) => action.debug_line(repacker),
            PcgAction::Owned(action) => action.debug_line(repacker),
        }
    }
}

impl<'tcx> ToJsonWithCompilerCtxt<'tcx> for PcgAction<'tcx> {
    fn to_json(&self, repacker: CompilerCtxt<'_, 'tcx>) -> serde_json::Value {
        match self {
            PcgAction::Borrow(action) => action.to_json(repacker),
            PcgAction::Owned(action) => action.to_json(),
        }
    }
}
