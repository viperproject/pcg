use std::collections::BTreeMap;

use serde_json::json;

use crate::rustc_interface::{
    data_structures::fx::FxHashMap,
    middle::{mir::BasicBlock, ty},
};
use crate::utils::display::{DebugLines, DisplayWithCompilerCtxt};
use crate::utils::{Place, CompilerCtxt, SnapshotLocation};

use crate::utils::json::ToJsonWithCompilerCtxt;

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

impl<'tcx> ToJsonWithCompilerCtxt<'tcx> for Latest<'tcx> {
    fn to_json(&self, repacker: CompilerCtxt<'_, 'tcx>) -> serde_json::Value {
        json!(self
            .0
            .iter()
            .map(|(p, l)| {
                let ty = p.ty(repacker).ty;
                let ty_str = if let ty::TyKind::Ref(region, ty, mutbl) = ty.kind() {
                    format!(
                        "&{}{} {}",
                        region,
                        if mutbl.is_mut() { " mut" } else { "" },
                        ty
                    )
                } else {
                    format!("{}", ty)
                };
                (
                    format!("{}: {}", p.to_short_string(repacker), ty_str),
                    format!("{:?}", l),
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

    pub(crate) fn singleton(place: Place<'tcx>, location: SnapshotLocation) -> Self {
        let mut latest = Self::new();
        latest.insert(place, location);
        latest
    }

    fn get_exact(&self, place: Place<'tcx>) -> Option<SnapshotLocation> {
        self.0.get(&place).copied()
    }

    fn get_opt(&self, place: Place<'tcx>) -> Option<SnapshotLocation> {
        if let Some(location) = self.get_exact(place) {
            Some(location)
        } else {
            for (place, _) in place.iter_projections().rev() {
                if let Some(location) = self.get_exact(place.into()) {
                    return Some(location);
                }
            }
            None
        }
    }

    pub fn get(&self, place: Place<'tcx>) -> SnapshotLocation {
        self.get_opt(place).unwrap_or(SnapshotLocation::start())
    }

    pub (super) fn insert(
        &mut self,
        place: Place<'tcx>,
        location: SnapshotLocation,
    ) -> bool {
        self.insert_unchecked(place, location)
    }

    fn insert_unchecked(&mut self, place: Place<'tcx>, location: SnapshotLocation) -> bool {
        if self.get_exact(place) == Some(location) {
            return false;
        }

        self.0.retain(|existing, loc| {

            // After insertion of this place, if we were to lookup `existing`,
            // we'd get this location for `place`. For example if existing is `x.f.g`
            // and place is `x.f`, then `Latest::get_opt(x.f.g)` would not find `x.f.g` and
            // return the location for `x.f`.
            if place.is_prefix(*existing) {
                return false;
            }

            // Places that we're a prefix of should be updated to this new location.
            // For example if existing is `x` and place is `x.f`, then we should
            // snapshot `x` to this location. However, the snapshot for e.g. `x.g` would
            // keep its old label.
            if existing.is_prefix(place) && *loc != location {
                *loc = location;
            }
            true
        });
        self.0.insert(place, location);
        true
    }

    pub fn join(
        &mut self,
        other: &Self,
        block: BasicBlock,
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
            if let Some(self_loc) = self.get_opt(*place) {
                if self_loc != *other_loc {
                    self.insert_unchecked(*place, SnapshotLocation::Start(block));
                    changed = true;
                }
            } else {
                self.insert(*place, *other_loc);
                changed = true;
            }
        }
        changed
    }
}
