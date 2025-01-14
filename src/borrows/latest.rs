use std::collections::BTreeMap;

use serde_json::json;

use crate::rustc_interface::middle::{ty, mir::BasicBlock};
use crate::utils::{Place, PlaceRepacker, SnapshotLocation};

use super::domain::ToJsonWithRepacker;

#[derive(Clone, Debug)]
pub struct Latest<'tcx>(Vec<(Place<'tcx>, SnapshotLocation)>);

impl<'tcx> ToJsonWithRepacker<'tcx> for Latest<'tcx> {
    fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
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
                (format!("{}: {}", p.to_short_string(repacker), ty_str), format!("{:?}", l))
            })
            .collect::<BTreeMap<_, _>>())
    }
}

impl<'tcx> Latest<'tcx> {
    pub fn new() -> Self {
        Self(Vec::new())
    }

    fn get_exact(&self, place: Place<'tcx>) -> Option<SnapshotLocation> {
        self.0.iter().find(|(p, _)| *p == place).map(|(_, l)| *l)
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

    pub fn insert(
        &mut self,
        place: Place<'tcx>,
        location: SnapshotLocation,
        _repacker: PlaceRepacker<'_, 'tcx>,
    ) {
        // TODO: Should this assertion pass?
        // if let Some(existing) = self.get_opt(place) {
        //     if existing != location && !place.has_location_dependent_value(repacker) {
        //         panic!(
        //             "location changed for place with location-independent value: {:?} -> {:?}",
        //             existing, location
        //         );
        //     }
        // }
        self.insert_unchecked(place, location);
    }

    fn insert_unchecked(&mut self, place: Place<'tcx>, location: SnapshotLocation) {
        self.0.retain(|(p, _)| !place.is_prefix(*p));
        for (p, loc) in self.0.iter_mut() {
            if p.is_prefix(place) {
                *loc = location;
            }
        }
        self.0.push((place, location));
    }

    pub fn join(
        &mut self,
        other: &Self,
        block: BasicBlock,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        let mut changed = false;
        for (place, other_loc) in other.0.iter() {
            if let Some(self_loc) = self.get_opt(*place) {
                if self_loc != *other_loc {
                    self.insert_unchecked(*place, SnapshotLocation::Start(block));
                    changed = true;
                }
            } else {
                self.insert(*place, *other_loc, repacker);
                changed = true;
            }
        }
        changed
    }
}

impl<'tcx> PartialEq for Latest<'tcx> {
    fn eq(&self, other: &Self) -> bool {
        for (p, _) in self.0.iter() {
            if other.get(*p) != self.get(*p) {
                return false;
            }
        }
        for (p, _) in other.0.iter() {
            if other.get(*p) != self.get(*p) {
                return false;
            }
        }
        true
    }
}

impl<'tcx> Eq for Latest<'tcx> {}
