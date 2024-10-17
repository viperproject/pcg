use std::collections::BTreeMap;

use crate::rustc_interface::middle::mir::{BasicBlock, Local, Location};
use crate::utils::{Place, SnapshotLocation};

#[derive(Clone, Debug)]
pub struct Latest<'tcx>(Vec<(Place<'tcx>, SnapshotLocation)>);

impl<'tcx> Latest<'tcx> {
    pub fn new() -> Self {
        Self(Vec::new())
    }

    fn get_exact(&self, place: Place<'tcx>) -> Option<SnapshotLocation> {
        self.0.iter().find(|(p, _)| *p == place).map(|(_, l)| *l)
    }
    pub fn get_opt(&self, place: Place<'tcx>) -> Option<SnapshotLocation> {
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

    pub fn insert(&mut self, place: Place<'tcx>, location: SnapshotLocation) {
        self.0.retain(|(p, _)| !place.is_prefix(*p));
        for (p, loc) in self.0.iter_mut() {
            if p.is_prefix(place) {
                *loc = location;
            }
        }
        self.0.push((place, location));
    }

    pub fn join(&mut self, other: &Self, block: BasicBlock) -> bool {
        let mut changed = false;
        for (place, other_loc) in other.0.iter() {
            if let Some(self_loc) = self.get_opt(*place) {
                if self_loc != *other_loc {
                    self.insert(*place, SnapshotLocation::Join(block));
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
