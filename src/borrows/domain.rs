use std::rc::Rc;

use rustc_interface::{
    borrowck::{
        borrow_set::BorrowSet,
        consumers::BorrowIndex
    },
    data_structures::fx::{FxHashMap, FxHashSet},
    dataflow::{AnalysisDomain, JoinSemiLattice},
    middle::mir::{self, Location},
};

use crate::{rustc_interface, utils::Place};

impl<'tcx> JoinSemiLattice for BorrowsDomain<'tcx> {
    fn join(&mut self, other: &Self) -> bool {
        let mut changed = false;
        for borrow in &other.live_borrows {
            if self.live_borrows.insert(borrow.clone()) {
                changed = true;
            }
        }
        for region_abstraction in &other.region_abstractions {
            if !self.region_abstractions.contains(region_abstraction) {
                self.region_abstractions.push(region_abstraction.clone());
                changed = true;
            }
        }
        for action in &other.actions {
            if !self.actions.contains(action) {
                self.actions.insert(action.clone());
            }
        }
        changed
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct RegionAbstraction<'tcx> {
    pub loans_in: FxHashSet<mir::Place<'tcx>>,
    pub loans_out: FxHashSet<mir::Place<'tcx>>,
}

impl<'tcx> RegionAbstraction<'tcx> {
    pub fn new() -> Self {
        Self {
            loans_in: FxHashSet::default(),
            loans_out: FxHashSet::default(),
        }
    }

    pub fn add_loan_in(&mut self, loan: mir::Place<'tcx>) {
        self.loans_in.insert(loan);
    }

    pub fn add_loan_out(&mut self, loan: mir::Place<'tcx>) {
        self.loans_out.insert(loan);
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct Borrow<'tcx> {
    pub kind: BorrowKind<'tcx>,
    pub before: Option<Location>,
}

impl<'tcx> Borrow<'tcx> {
    pub fn new(kind: BorrowKind<'tcx>, before: Option<Location>) -> Self {
        Self { kind, before }
    }

    pub fn assigned_place(&self, borrow_set: &BorrowSet<'tcx>) -> Place<'tcx> {
        self.kind.assigned_place(borrow_set)
    }

    pub fn borrowed_place(&self, borrow_set: &BorrowSet<'tcx>) -> Place<'tcx> {
        self.kind.borrowed_place(borrow_set)
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub enum BorrowKind<'tcx> {
    Rustc(BorrowIndex),
    PCS {
        borrowed_place: Place<'tcx>,
        assigned_place: Place<'tcx>,
    }
}

impl<'tcx> BorrowKind<'tcx> {
    pub fn assigned_place(&self, borrow_set: &BorrowSet<'tcx>) -> Place<'tcx> {
        match self {
            BorrowKind::Rustc(borrow_index) => borrow_set[*borrow_index].assigned_place.into(),
            BorrowKind::PCS { assigned_place, .. } => *assigned_place,
        }
    }

    pub fn borrowed_place(&self, borrow_set: &BorrowSet<'tcx>) -> Place<'tcx> {
        match self {
            BorrowKind::Rustc(borrow_index) => borrow_set[*borrow_index].borrowed_place.into(),
            BorrowKind::PCS { borrowed_place, .. } => *borrowed_place,
        }
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct BorrowsDomain<'tcx> {
    pub live_borrows: FxHashSet<Borrow<'tcx>>,
    pub region_abstractions: Vec<RegionAbstraction<'tcx>>,
    pub actions: FxHashSet<String>
}

impl<'tcx> BorrowsDomain<'tcx> {
    pub fn new() -> Self {
        Self {
            live_borrows: FxHashSet::default(),
            region_abstractions: vec![],
            actions: FxHashSet::default(),
        }
    }

    pub fn log_action(&mut self, action: String) {
        self.actions.insert(action);
    }

    pub fn add_region_abstraction(&mut self, abstraction: RegionAbstraction<'tcx>) {
        if !self.region_abstractions.contains(&abstraction) {
            self.region_abstractions.push(abstraction);
        }
    }

    pub fn add_borrow(&mut self, borrow: Borrow<'tcx>) {
        self.live_borrows.insert(borrow);
    }

    pub fn add_rustc_borrow(&mut self, borrow: BorrowIndex) {
        self.live_borrows.insert(Borrow {
            kind: BorrowKind::Rustc(borrow),
            before: None,
        });
    }

    pub fn remove_borrow(&mut self, borrow: &BorrowIndex) {
        self.live_borrows.remove(&Borrow {
            kind: BorrowKind::Rustc(*borrow),
            before: None,
        });
    }
}