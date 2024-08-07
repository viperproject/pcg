use std::rc::Rc;

use rustc_interface::{
    ast::Mutability,
    borrowck::{borrow_set::BorrowSet, consumers::BorrowIndex},
    data_structures::{
        fx::{FxHashMap, FxHashSet},
        graph::dominators::Dominators,
    },
    dataflow::{AnalysisDomain, JoinSemiLattice},
    middle::mir::{self, tcx::PlaceTy, BasicBlock, Local, Location, VarDebugInfo},
    middle::ty::{self, RegionVid, TyCtxt},
};
use serde_json::{json, Value};

use crate::{
    combined_pcs::PlaceCapabilitySummary,
    free_pcs::{
        CapabilityKind, CapabilityLocal, CapabilityProjections, CapabilitySummary,
        FreePlaceCapabilitySummary,
    },
    rustc_interface,
    utils::{Place, PlaceRepacker, PlaceSnapshot},
    ReborrowBridge,
};

use super::{
    borrows_visitor::DebugCtx,
    deref_expansions::{self, DerefExpansions},
    domain::{Borrow, DerefExpansion, Latest, MaybeOldPlace, Reborrow, RegionAbstraction},
    reborrowing_dag::ReborrowingDag,
    unblock_graph::UnblockGraph,
};

impl<'mir, 'tcx> JoinSemiLattice for BorrowsState<'mir, 'tcx> {
    fn join(&mut self, other: &Self) -> bool {
        let mut changed = false;
        for region_abstraction in other.region_abstractions.iter() {
            if self.region_abstractions.insert(region_abstraction.clone()) {
                changed = true;
            }
        }
        for reborrow in other.reborrows.iter() {
            if self.reborrows.insert(reborrow.clone()) {
                changed = true;
            }
        }
        if self.deref_expansions.join(&other.deref_expansions) {
            changed = true;
        }
        if self.latest.join(&other.latest, self.body) {
            changed = true;
        }
        changed
    }
}

#[derive(Clone, Debug)]
pub struct RegionAbstractions<'tcx>(Vec<RegionAbstraction<'tcx>>);

impl<'tcx> RegionAbstractions<'tcx> {
    pub fn new() -> Self {
        Self(vec![])
    }

    pub fn contains(&self, abstraction: &RegionAbstraction<'tcx>) -> bool {
        self.0.contains(abstraction)
    }

    pub fn filter_for_path(&mut self, path: &[BasicBlock]) {
        self.0
            .retain(|abstraction| path.contains(&abstraction.location().block));
    }

    pub fn make_place_old(&mut self, place: Place<'tcx>, latest: &Latest<'tcx>) {
        for abstraction in &mut self.0 {
            abstraction.make_place_old(place, latest);
        }
    }

    pub fn blocks(&self, place: &MaybeOldPlace<'tcx>) -> bool {
        self.0.iter().any(|abstraction| abstraction.blocks(place))
    }

    pub fn insert(&mut self, abstraction: RegionAbstraction<'tcx>) -> bool {
        if !self.0.contains(&abstraction) {
            self.0.push(abstraction);
            true
        } else {
            false
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = &RegionAbstraction<'tcx>> {
        self.0.iter()
    }
    pub fn delete_region(&mut self, location: Location) {
        self.0
            .retain(|abstraction| abstraction.location() != location);
    }
}
#[derive(Clone, Debug)]
pub struct BorrowsState<'mir, 'tcx> {
    body: &'mir mir::Body<'tcx>,
    latest: Latest<'tcx>,
    pub reborrows: ReborrowingDag<'tcx>,
    pub region_abstractions: RegionAbstractions<'tcx>,
    pub deref_expansions: DerefExpansions<'tcx>,
    pub logs: Vec<String>,
}

impl<'mir, 'tcx> PartialEq for BorrowsState<'mir, 'tcx> {
    fn eq(&self, other: &Self) -> bool {
        self.reborrows == other.reborrows
            && self.deref_expansions == other.deref_expansions
            && self.latest == other.latest
    }
}

impl<'mir, 'tcx> Eq for BorrowsState<'mir, 'tcx> {}

fn deref_expansions_should_be_considered_same<'tcx>(
    exp1: &DerefExpansion<'tcx>,
    exp2: &DerefExpansion<'tcx>,
) -> bool {
    match (exp1, exp2) {
        (
            DerefExpansion::OwnedExpansion { base: b1, .. },
            DerefExpansion::OwnedExpansion { base: b2, .. },
        ) => b1 == b2,
        (DerefExpansion::BorrowExpansion(b1), DerefExpansion::BorrowExpansion(b2)) => b1 == b2,
        _ => false,
    }
}

fn subtract_deref_expansions<'tcx>(
    from: &DerefExpansions<'tcx>,
    to: &DerefExpansions<'tcx>,
) -> FxHashSet<DerefExpansion<'tcx>> {
    from.iter()
        .filter(|f1| {
            to.iter()
                .all(|f2| !deref_expansions_should_be_considered_same(f1, f2))
        })
        .cloned()
        .collect()
}

impl<'mir, 'tcx> BorrowsState<'mir, 'tcx> {
    pub fn filter_for_live_origins(&mut self, origins: &[RegionVid]) {}
    pub fn filter_for_path(&mut self, path: &[BasicBlock]) {
        self.reborrows.filter_for_path(path);
        self.deref_expansions.filter_for_path(path);
        self.region_abstractions.filter_for_path(path);
    }
    pub fn bridge(&self, to: &Self, block: BasicBlock, tcx: TyCtxt<'tcx>) -> ReborrowBridge<'tcx> {
        let repacker = PlaceRepacker::new(self.body, tcx);
        let added_reborrows: FxHashSet<Reborrow<'tcx>> = to
            .reborrows()
            .iter()
            .filter(|rb| !self.has_reborrow_at_location(rb.location))
            .cloned()
            .collect();
        let expands = subtract_deref_expansions(&to.deref_expansions, &self.deref_expansions);

        let mut ug = UnblockGraph::new();

        for reborrow in self.reborrows().iter() {
            if !to.has_reborrow_at_location(reborrow.location) {
                ug.kill_reborrow(*reborrow, self, block, repacker);
            }
        }

        for exp in subtract_deref_expansions(&self.deref_expansions, &to.deref_expansions) {
            ug.unblock_place(exp.base(), self, block, repacker);
        }

        for abstraction in self.region_abstractions.iter() {
            if !to.region_abstractions.contains(&abstraction) {
                ug.kill_abstraction(
                    self,
                    &abstraction.abstraction_type,
                    PlaceRepacker::new(self.body, tcx),
                );
            }
        }

        ReborrowBridge {
            added_reborrows,
            expands,
            ug,
        }
    }

    pub fn ensure_deref_expansions_to_fpcs(
        &mut self,
        tcx: TyCtxt<'tcx>,
        body: &mir::Body<'tcx>,
        summary: &CapabilitySummary<'tcx>,
        location: Location,
    ) {
        for c in (*summary).iter() {
            match c {
                CapabilityLocal::Allocated(projections) => {
                    for (place, kind) in (*projections).iter() {
                        match kind {
                            CapabilityKind::Exclusive => {
                                if place.is_ref(body, tcx) {
                                    self.deref_expansions.ensure_deref_expansion_to_at_least(
                                        &MaybeOldPlace::Current {
                                            place: place
                                                .project_deref(PlaceRepacker::new(body, tcx)),
                                        },
                                        body,
                                        tcx,
                                        location,
                                    );
                                } else {
                                    let mut ug = UnblockGraph::new();
                                    for deref_expansion in self
                                        .deref_expansions
                                        .descendants_of(MaybeOldPlace::Current { place: *place })
                                    {
                                        ug.kill_place(
                                            deref_expansion.base(),
                                            self,
                                            location.block,
                                            PlaceRepacker::new(body, tcx),
                                        );
                                    }
                                    self.apply_unblock_graph(ug, tcx);
                                }
                            }
                            _ => {}
                        }
                    }
                }
                _ => {}
            }
        }
    }

    pub fn get_abstractions_blocking(
        &self,
        place: &MaybeOldPlace<'tcx>,
    ) -> Vec<&RegionAbstraction<'tcx>> {
        self.region_abstractions
            .iter()
            .filter(|abstraction| abstraction.blocks(place))
            .collect()
    }

    pub fn ensure_expansion_to_exactly(
        &mut self,
        tcx: TyCtxt<'tcx>,
        body: &mir::Body<'tcx>,
        place: MaybeOldPlace<'tcx>,
        location: Location,
    ) {
        let mut ug = UnblockGraph::new();
        ug.unblock_place(place, self, location.block, PlaceRepacker::new(body, tcx));
        self.apply_unblock_graph(ug, tcx);

        // Originally we may not have been expanded enough
        self.deref_expansions
            .ensure_expansion_to_exactly(place, body, tcx, location);
    }

    pub fn roots_of(
        &self,
        place: &MaybeOldPlace<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> FxHashSet<MaybeOldPlace<'tcx>> {
        let mut result = FxHashSet::default();
        for place in self.reborrows.get_places_blocking(place) {
            result.extend(self.roots_of(&place, repacker));
        }
        for place in self.deref_expansions.get_parents(place, repacker) {
            result.extend(self.roots_of(&place, repacker));
        }
        if result.is_empty() {
            result.insert(place.clone());
        }
        result
    }

    pub fn remove_dangling_old_places(&mut self, tcx: TyCtxt<'tcx>) {
        while self.remove_dangling_old_places_pass(tcx) {}
    }

    pub fn is_leaf(&self, place: &MaybeOldPlace<'tcx>) -> bool {
        !self.region_abstractions.blocks(place)
            && self.reborrows.get_places_blocking(place).is_empty()
            && !self.deref_expansions.contains_expansion_from(place)
    }

    /// Reborrows and deref expansions that form the "interface" of the graph: the graph
    /// could be extended via these.
    pub fn leaves(
        &self,
        tcx: TyCtxt<'tcx>,
    ) -> (FxHashSet<&Reborrow<'tcx>>, FxHashSet<&DerefExpansion<'tcx>>) {
        let mut reborrows: FxHashSet<_> = self.reborrows.iter().collect();
        let mut deref_expansions: FxHashSet<_> = self.deref_expansions.iter().collect();
        reborrows.retain(|rb| self.is_leaf(&rb.assigned_place));
        deref_expansions.retain(|de| {
            de.expansion(PlaceRepacker::new(self.body, tcx))
                .iter()
                .all(|e| self.is_leaf(e))
        });
        return (reborrows, deref_expansions);
    }

    // TODO: This is not precise, consider each location separately
    pub fn remove_dangling_old_places_pass(&mut self, tcx: TyCtxt<'tcx>) -> bool {
        let mut changed = false;
        let (reborrows, deref_expansions) = self.leaves(tcx);
        let mut reborrows = reborrows
            .into_iter()
            .cloned()
            .collect::<FxHashSet<Reborrow<'tcx>>>();
        let mut deref_expansions = deref_expansions
            .into_iter()
            .cloned()
            .collect::<FxHashSet<DerefExpansion<'tcx>>>();
        for rb in reborrows {
            if !rb.assigned_place.is_current() {
                if self.reborrows.remove(&rb) {
                    changed = true;
                }
            }
        }
        for de in deref_expansions {
            if !de.base().is_current() {
                if self.deref_expansions.remove(&de) {
                    changed = true;
                }
            }
        }
        changed
    }

    /// Returns places in the PCS that are reborrowed
    pub fn reborrow_roots(&self, repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<Place<'tcx>> {
        self.reborrows
            .roots()
            .into_iter()
            .flat_map(|place| self.roots_of(&place, repacker))
            .flat_map(|place| match place {
                MaybeOldPlace::Current { place } => Some(place),
                MaybeOldPlace::OldPlace(_) => None,
            })
            .collect()
    }

    pub fn apply_unblock_graph(&mut self, graph: UnblockGraph<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
        let mut changed = false;
        eprintln!("Applying unblock graph {:?}", graph);
        for action in graph.actions(tcx) {
            match action {
                crate::combined_pcs::UnblockAction::TerminateReborrow {
                    blocked_place,
                    assigned_place,
                    ..
                } => {
                    if self.reborrows.kill_reborrows(blocked_place, assigned_place) {
                        changed = true;
                    }
                }
                crate::combined_pcs::UnblockAction::Collapse(place, _) => {
                    if self.deref_expansions.delete_descendants_of(
                        place,
                        PlaceRepacker::new(self.body, tcx),
                        None,
                    ) {
                        changed = true;
                    }
                }
                crate::combined_pcs::UnblockAction::TerminateAbstraction(location, call) => {
                    self.region_abstractions.delete_region(location);
                    // match call {
                    //     super::domain::AbstractionType::FunctionCall { location, def_id, substs, blocks_args, blocked_place } => todo!(),
                    // }
                }
            }
        }
        changed
    }

    pub fn reborrows(&self) -> &ReborrowingDag<'tcx> {
        &self.reborrows
    }

    pub fn set_latest(&mut self, place: Place<'tcx>, location: Location) {
        self.latest.insert(place, location);
    }

    pub fn get_latest(&self, place: &Place<'tcx>) -> Location {
        self.latest.get(place)
    }

    pub fn reborrows_blocking(&self, place: MaybeOldPlace<'tcx>) -> FxHashSet<&Reborrow<'tcx>> {
        self.reborrows
            .iter()
            .filter(|rb| rb.blocked_place == place)
            .collect()
    }

    pub fn reborrows_assigned_to(&self, place: MaybeOldPlace<'tcx>) -> FxHashSet<&Reborrow<'tcx>> {
        self.reborrows
            .iter()
            .filter(|rb| rb.assigned_place == place)
            .collect()
    }

    pub fn kill_reborrows_blocking(&mut self, place: MaybeOldPlace<'tcx>) {
        self.reborrows.kill_reborrows_blocking(place);
    }

    pub fn move_reborrows(
        &mut self,
        orig_assigned_place: Place<'tcx>,
        new_assigned_place: Place<'tcx>,
    ) {
        self.reborrows.move_reborrows(
            MaybeOldPlace::Current {
                place: orig_assigned_place,
            },
            MaybeOldPlace::Current {
                place: new_assigned_place,
            },
        );
    }

    pub fn add_reborrow(
        &mut self,
        blocked_place: Place<'tcx>,
        assigned_place: Place<'tcx>,
        mutability: Mutability,
        location: Location,
        region: ty::Region<'tcx>,
    ) {
        self.reborrows
            .add_reborrow(blocked_place, assigned_place, mutability, location, region);
        self.log("Add reborrow".to_string());
    }

    pub fn contains_reborrow(&self, reborrow: &Reborrow<'tcx>) -> bool {
        self.reborrows.contains(reborrow)
    }

    pub fn has_reborrow_at_location(&self, location: Location) -> bool {
        self.reborrows.has_reborrow_at_location(location)
    }

    pub fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> Value {
        json!({})
    }

    pub fn new(body: &'mir mir::Body<'tcx>) -> Self {
        Self {
            body,
            deref_expansions: DerefExpansions::new(),
            latest: Latest::new(),
            reborrows: ReborrowingDag::new(),
            region_abstractions: RegionAbstractions::new(),
            logs: vec![],
        }
    }

    fn log(&mut self, log: String) {
        self.logs.push(log);
    }

    pub fn is_current(&self, place: &PlaceSnapshot<'tcx>, body: &mir::Body<'tcx>) -> bool {
        let last_loc = self.latest.get(&place.place);
        let result = if last_loc.block == place.at.block {
            last_loc.statement_index <= place.at.statement_index
        } else {
            body.basic_blocks
                .dominators()
                .dominates(last_loc.block, place.at.block)
        };
        if !result {
            eprintln!(
                "is_current({:?}) = {:?} <{:?}>",
                place,
                result,
                self.latest.get(&place.place)
            );
        }
        result
    }

    pub fn add_region_abstraction(&mut self, abstraction: RegionAbstraction<'tcx>) {
        self.region_abstractions.insert(abstraction);
    }

    pub fn make_place_old(
        &mut self,
        place: Place<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
        debug_ctx: Option<DebugCtx>,
    ) {
        self.reborrows
            .make_place_old(place, &self.latest, debug_ctx);
        self.deref_expansions.make_place_old(place, &self.latest);
        self.region_abstractions.make_place_old(place, &self.latest);
    }

    pub fn remove_borrow(&mut self, tcx: TyCtxt<'tcx>, borrow: &Borrow<'tcx>, block: BasicBlock) {
        let mut g = UnblockGraph::new();

        g.unblock_place(
            MaybeOldPlace::Current {
                place: borrow.borrowed_place,
            },
            &self,
            block,
            PlaceRepacker::new(self.body, tcx),
        );

        self.apply_unblock_graph(g, tcx);
    }

    pub fn remove_rustc_borrow(
        &mut self,
        tcx: TyCtxt<'tcx>,
        rustc_borrow: &BorrowIndex,
        borrow_set: &BorrowSet<'tcx>,
        body: &mir::Body<'tcx>,
        block: BasicBlock,
    ) {
        let borrow = &borrow_set[*rustc_borrow];
        let borrow = Borrow::new(
            borrow.borrowed_place.into(),
            borrow.assigned_place.into(),
            matches!(borrow.kind, mir::BorrowKind::Mut { .. }),
        );
        self.remove_borrow(tcx, &borrow, block)
    }
    pub fn remove_loans_assigned_to(
        &mut self,
        tcx: TyCtxt<'tcx>,
        borrow_set: &BorrowSet<'tcx>,
        place: Place<'tcx>,
        block: BasicBlock,
    ) {
        for (idx, borrow) in borrow_set.location_map.iter() {
            let assigned_place: Place<'tcx> = borrow.assigned_place.into();
            if assigned_place == place {
                self.remove_borrow(
                    tcx,
                    &Borrow::new(
                        borrow.borrowed_place.into(),
                        borrow.assigned_place.into(),
                        matches!(borrow.kind, mir::BorrowKind::Mut { .. }),
                    ),
                    block,
                );
            }
        }
    }
}
