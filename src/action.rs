use derive_more::{Deref, DerefMut, From};
use serde_json::Map;

use crate::{
    borrow_pcg::{
        action::{actions::BorrowPCGActions, BorrowPcgActionKind},
        unblock_graph::BorrowPCGUnblockAction,
    },
    free_pcs::{CapabilityKind, RepackOp},
    utils::{display::DisplayWithCompilerCtxt, json::ToJsonWithCompilerCtxt, CompilerCtxt, Place},
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

impl<'tcx> From<Vec<OwnedPcgAction<'tcx>>> for PcgActions<'tcx> {
    fn from(actions: Vec<OwnedPcgAction<'tcx>>) -> Self {
        PcgActions(actions.into_iter().map(|a| a.into()).collect::<Vec<_>>())
    }
}

impl<'tcx> PcgActions<'tcx> {
    pub(crate) fn extend(&mut self, actions: PcgActions<'tcx>) {
        self.0.extend(actions.0);
    }

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

    pub fn owned_pcg_actions(&self) -> Vec<&OwnedPcgAction<'tcx>> {
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
                PcgAction::Borrow(BorrowPcgAction {
                    kind: BorrowPcgActionKind::RemoveEdge(edge),
                    ..
                }) => Some(edge.clone().into()),
                _ => None,
            })
            .collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ActionKindWithDebugCtxt<T> {
    pub(crate) kind: T,
    pub(crate) debug_context: Option<String>,
}

impl<'tcx, T: DisplayWithCompilerCtxt<'tcx>> ActionKindWithDebugCtxt<T> {
    pub(crate) fn new(kind: T, debug_context: Option<String>) -> Self {
        Self {
            kind,
            debug_context,
        }
    }

    pub(crate) fn debug_line(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> String {
        self.kind.to_short_string(ctxt)
    }
}

impl<'tcx, T: DisplayWithCompilerCtxt<'tcx>> ToJsonWithCompilerCtxt<'tcx>
    for ActionKindWithDebugCtxt<T>
{
    fn to_json(&self, repacker: CompilerCtxt<'_, 'tcx>) -> serde_json::Value {
        let mut map = Map::new();
        map.insert(
            "kind".to_string(),
            self.kind.to_short_string(repacker).into(),
        );
        if let Some(debug_context) = &self.debug_context {
            map.insert(
                "debug_context".to_string(),
                debug_context.to_string().into(),
            );
        } else {
            map.insert("debug_context".to_string(), serde_json::Value::Null);
        }
        map.into()
    }
}

pub type OwnedPcgAction<'tcx> = ActionKindWithDebugCtxt<RepackOp<'tcx>>;

/// An action that is applied to a `BorrowsState` during the dataflow analysis
/// of `BorrowsVisitor`, for which consumers (e.g. Prusti) may wish to perform
/// their own effect (e.g. for an unblock, applying a magic wand).
pub type BorrowPcgAction<'tcx> = ActionKindWithDebugCtxt<BorrowPcgActionKind<'tcx>>;

#[allow(clippy::large_enum_variant)]
#[derive(Clone, PartialEq, Eq, Debug, From)]
pub enum PcgAction<'tcx> {
    Borrow(BorrowPcgAction<'tcx>),
    Owned(OwnedPcgAction<'tcx>),
}

impl<'tcx> PcgAction<'tcx> {
    pub(crate) fn restore_capability(
        place: Place<'tcx>,
        capability: CapabilityKind,
        debug_context: impl Into<String>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Self {
        if place.is_owned(ctxt) {
            PcgAction::Owned(
                OwnedPcgAction {
                    kind: RepackOp::RegainLoanedCapability(place, capability),
                    debug_context: Some(debug_context.into()),
                }
                .into(),
            )
        } else {
            BorrowPcgAction::restore_capability(place, capability, debug_context).into()
        }
    }

    pub(crate) fn debug_line(&self, repacker: CompilerCtxt<'_, 'tcx>) -> String {
        match self {
            PcgAction::Borrow(action) => action.debug_line(repacker),
            PcgAction::Owned(action) => action.debug_line(repacker),
        }
    }
}

impl<'tcx> ToJsonWithCompilerCtxt<'tcx> for PcgAction<'tcx> {
    fn to_json(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> serde_json::Value {
        match self {
            PcgAction::Borrow(action) => action.to_json(ctxt),
            PcgAction::Owned(action) => action.to_json(ctxt),
        }
    }
}
