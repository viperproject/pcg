//! Logic related to storing "last-modified" locations for places in the PCG.
use std::collections::BTreeMap;

use serde_json::json;

use crate::rustc_interface::{
    data_structures::fx::FxHashMap,
    middle::{mir::BasicBlock, ty},
};
use crate::utils::display::{DebugLines, DisplayWithCompilerCtxt};
use crate::utils::{CompilerCtxt, Place, SnapshotLocation};

use crate::utils::json::ToJsonWithCompilerCtxt;

/// A map from places to their last-modified locations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Latest<'tcx>(FxHashMap<Place<'tcx>, SnapshotLocation>);

impl<'tcx> DebugLines<CompilerCtxt<'_, 'tcx>> for Latest<'tcx> {
    fn debug_lines(&self, repacker: CompilerCtxt<'_, 'tcx>) -> Vec<String> {
        self.0
            .iter()
            .map(|(p, l)| format!("{} -> {:?}", p.to_short_string(repacker), l))
            .collect()
    }
}

impl<'tcx, BC: Copy> ToJsonWithCompilerCtxt<'tcx, BC> for Latest<'tcx> {
    fn to_json(&self, ctxt: CompilerCtxt<'_, 'tcx, BC>) -> serde_json::Value {
        json!(self
            .0
            .iter()
            .map(|(p, l)| {
                let ty = p.ty(ctxt).ty;
                let ty_str = if let ty::TyKind::Ref(region, ty, mutbl) = ty.kind() {
                    format!(
                        "&{}{} {}",
                        region,
                        if mutbl.is_mut() { " mut" } else { "" },
                        ty
                    )
                } else {
                    format!("{ty}")
                };
                (
                    format!("{}: {}", p.to_short_string(ctxt), ty_str),
                    format!("{l:?}"),
                )
            })
            .collect::<BTreeMap<_, _>>())
    }
}

impl Default for Latest<'_> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'tcx> Latest<'tcx> {
    pub fn new() -> Self {
        Self(FxHashMap::default())
    }

    fn get_opt(
        &self,
        place: Place<'tcx>,
        _ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Option<SnapshotLocation> {
        self.0
            .iter()
            .find_map(|(p, l)| {
                if p.conflicts_with(place) {
                    Some(l)
                } else {
                    None
                }
            })
            .copied()
    }

    /// Get the last-modified location for a place
    pub fn get(&self, place: Place<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) -> SnapshotLocation {
        self.get_opt(place, ctxt)
            .unwrap_or(SnapshotLocation::start())
    }

    pub(super) fn insert(
        &mut self,
        place: Place<'tcx>,
        location: SnapshotLocation,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        if self.get_opt(place, ctxt) == Some(location) {
            return false;
        }
        self.0.retain(|existing, _| !existing.conflicts_with(place));
        self.0.insert(place, location);
        true
    }

    pub(crate) fn join(
        &mut self,
        other: &Self,
        block: BasicBlock,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        if self.0.is_empty() {
            if other.0.is_empty() {
                return false;
            } else {
                self.0 = other.0.clone();
                return true;
            }
        }
        let mut changed = false;
        for (place, other_loc) in other.0.iter() {
            if let Some(self_loc) = self.get_opt(*place, ctxt) {
                if self_loc != *other_loc {
                    self.insert(*place, SnapshotLocation::Start(block), ctxt);
                    changed = true;
                }
            } else {
                self.insert(*place, *other_loc, ctxt);
                changed = true;
            }
        }
        changed
    }
}
