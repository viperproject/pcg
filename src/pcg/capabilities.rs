use crate::{
    pcg_validity_assert,
    rustc_interface::index::{Idx, IndexVec},
    utils::data_structures::HashMap,
};
use std::{
    cell::RefCell,
    cmp::Ordering,
    fmt::{Debug, Formatter, Result},
};

use derive_more::From;

use crate::{
    pcg::PcgArena,
    utils::{Place, SnapshotLocation, data_structures::HashSet},
};

/// Macro for generating patterns that match a capability and all "greater" capabilities
/// according to the partial ordering.
///
/// Usage:
/// ```ignore
/// match cap {
///     capability_gte!(Read) => { /* matches Read or Exclusive */ }
///     capability_gte!(Write) => { /* matches Write, ShallowExclusive, or Exclusive */ }
///     capability_gte!(ShallowExclusive) => { /* matches ShallowExclusive or Exclusive */ }
///     capability_gte!(Exclusive) => { /* matches only Exclusive */ }
/// }
/// ```
///
/// Also supports single-letter abbreviations:
/// ```ignore
/// match cap {
///     capability_gte!(R) => { /* matches Read or Exclusive */ }
///     capability_gte!(W) => { /* matches Write, ShallowExclusive, or Exclusive */ }
///     capability_gte!(e) => { /* matches ShallowExclusive or Exclusive */ }
///     capability_gte!(E) => { /* matches only Exclusive */ }
/// }
/// ```
#[macro_export]
macro_rules! capability_gte {
    // Full names
    (Read) => {
        CapabilityKind::Read | CapabilityKind::Exclusive
    };
    (Write) => {
        CapabilityKind::Write | CapabilityKind::ShallowExclusive | CapabilityKind::Exclusive
    };
    (ShallowExclusive) => {
        CapabilityKind::ShallowExclusive | CapabilityKind::Exclusive
    };
    (Exclusive) => {
        CapabilityKind::Exclusive
    };

    // Single-letter abbreviations
    (R) => {
        CapabilityKind::Read | CapabilityKind::Exclusive
    };
    (W) => {
        CapabilityKind::Write | CapabilityKind::ShallowExclusive | CapabilityKind::Exclusive
    };
    (e) => {
        CapabilityKind::ShallowExclusive | CapabilityKind::Exclusive
    };
    (E) => {
        CapabilityKind::Exclusive
    };
}

#[allow(dead_code)]
pub(crate) enum ConstraintResult<'arena> {
    Unsat,
    Sat(Option<CapabilityConstraint<'arena>>),
}

#[allow(dead_code)]
impl ConstraintResult<'_> {
    pub(crate) fn is_sat(&self) -> bool {
        matches!(self, ConstraintResult::Sat(_))
    }
}

#[allow(dead_code)]
pub(crate) struct Choice {
    num_options: usize,
}

impl Choice {
    pub(crate) fn new(num_options: usize) -> Self {
        Self { num_options }
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub(crate) struct ChoiceIdx(usize);

impl Idx for ChoiceIdx {
    fn new(index: usize) -> Self {
        Self(index)
    }

    fn index(self) -> usize {
        self.0
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub(crate) struct Decision(usize);

impl Idx for Decision {
    fn new(index: usize) -> Self {
        Self(index)
    }

    fn index(self) -> usize {
        self.0
    }
}

#[allow(dead_code)]
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub(crate) enum CapabilityConstraint<'a> {
    Decision {
        choice: ChoiceIdx,
        decision: Decision,
    },
    Lt(SymbolicCapability, SymbolicCapability),
    #[allow(dead_code)]
    Lte(SymbolicCapability, SymbolicCapability),
    Eq(SymbolicCapability, SymbolicCapability),
    All(&'a [CapabilityConstraint<'a>]),
    Any(&'a [CapabilityConstraint<'a>]),
    Not(&'a CapabilityConstraint<'a>),
    False,
    True,
}

use CapabilityConstraint::*;
#[allow(dead_code)]
impl<'a> CapabilityConstraint<'a> {
    pub(crate) fn implies(self, other: Self, arena: PcgArena<'a>) -> Self {
        CapabilityConstraint::not(arena.alloc(self)).or(other, arena)
    }

    pub(crate) fn not(constraint: &'a CapabilityConstraint<'a>) -> Self {
        CapabilityConstraint::Not(constraint)
    }

    pub(crate) fn or(self, other: Self, arena: PcgArena<'a>) -> Self {
        CapabilityConstraint::Any(arena.alloc(vec![self, other]))
    }

    pub(crate) fn all(caps: &'a [CapabilityConstraint<'a>]) -> Self {
        CapabilityConstraint::All(caps)
    }

    pub(crate) fn and(self, other: Self, arena: PcgArena<'a>) -> Self {
        match (self, other) {
            (All(xs), All(ys)) => {
                All(arena.alloc(xs.iter().chain(ys.iter()).copied().collect::<Vec<_>>()))
            }
            _ => todo!(),
        }
    }

    pub(crate) fn all_read(places: &[SymbolicCapability], arena: PcgArena<'a>) -> Self {
        Self::all_eq(
            places,
            SymbolicCapability::Concrete(CapabilityKind::Read),
            arena,
        )
    }

    pub(crate) fn all_exclusive(places: &[SymbolicCapability], arena: PcgArena<'a>) -> Self {
        Self::all_eq(
            places,
            SymbolicCapability::Concrete(CapabilityKind::Exclusive),
            arena,
        )
    }

    pub(crate) fn all_eq(
        places: &[SymbolicCapability],
        cap: SymbolicCapability,
        arena: PcgArena<'a>,
    ) -> Self {
        let mut conds = HashSet::default();
        for place_cap in places.iter().copied() {
            match CapabilityConstraint::eq(place_cap, cap) {
                True => {}
                False => return False,
                result => {
                    conds.insert(result);
                }
            }
        }
        CapabilityConstraint::all(arena.alloc(conds.into_iter().collect::<Vec<_>>()))
    }

    pub(crate) fn lt(
        lhs: impl Into<SymbolicCapability>,
        rhs: impl Into<SymbolicCapability>,
    ) -> Self {
        CapabilityConstraint::Lt(lhs.into(), rhs.into())
    }

    pub(crate) fn eq(
        lhs: impl Into<SymbolicCapability>,
        rhs: impl Into<SymbolicCapability>,
    ) -> Self {
        CapabilityConstraint::Eq(lhs.into(), rhs.into())
    }

    #[allow(dead_code)]
    pub(crate) fn lte(
        lhs: impl Into<SymbolicCapability>,
        rhs: impl Into<SymbolicCapability>,
    ) -> Self {
        CapabilityConstraint::Lte(lhs.into(), rhs.into())
    }

    #[allow(dead_code)]
    pub(crate) fn gte(
        lhs: impl Into<SymbolicCapability>,
        rhs: impl Into<SymbolicCapability>,
    ) -> Self {
        CapabilityConstraint::Lte(rhs.into(), lhs.into())
    }
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct SymbolicCapabilityConstraints<'tcx>(HashSet<CapabilityConstraint<'tcx>>);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, From)]
pub struct CapabilityVar(usize);

pub(crate) struct Choices {
    choices: Vec<Choice>,
}

impl Choices {
    fn new() -> Self {
        Self { choices: vec![] }
    }
    fn add_choice(&mut self, choice: Choice) -> ChoiceIdx {
        self.choices.push(choice);
        ChoiceIdx(self.choices.len() - 1)
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub(crate) struct PlaceAtLocation<'tcx> {
    place: Place<'tcx>,
    location: SnapshotLocation,
}

impl<'tcx> PlaceAtLocation<'tcx> {
    fn new(place: Place<'tcx>, location: SnapshotLocation) -> Self {
        Self { place, location }
    }
}

pub(crate) struct CapabilityVars<'tcx>(Vec<PlaceAtLocation<'tcx>>);

impl<'tcx> CapabilityVars<'tcx> {
    fn contains(&self, pl: PlaceAtLocation<'tcx>) -> bool {
        self.0.iter().any(|p| *p == pl)
    }

    fn insert(&mut self, pl: PlaceAtLocation<'tcx>) -> CapabilityVar {
        pcg_validity_assert!(!self.contains(pl));
        self.0.push(pl);
        CapabilityVar(self.0.len() - 1)
    }
}

#[allow(dead_code)]
#[derive(Clone, Copy)]
pub(crate) struct SymbolicCapabilityCtxt<'a, 'tcx> {
    constraints: &'a RefCell<SymbolicCapabilityConstraints<'a>>,
    vars: &'a RefCell<CapabilityVars<'tcx>>,
    choices: &'a RefCell<Choices>,
}

#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum IntroduceConstraints<'tcx> {
    ExpandForSharedBorrow {
        base_place: Place<'tcx>,
        expansion_places: Vec<Place<'tcx>>,
        before_location: SnapshotLocation,
        after_location: SnapshotLocation,
    },
}

#[allow(dead_code)]
impl<'tcx> IntroduceConstraints<'tcx> {
    pub(crate) fn before_location(&self) -> SnapshotLocation {
        match self {
            IntroduceConstraints::ExpandForSharedBorrow {
                before_location, ..
            } => *before_location,
        }
    }

    pub(crate) fn after_location(&self) -> SnapshotLocation {
        match self {
            IntroduceConstraints::ExpandForSharedBorrow { after_location, .. } => *after_location,
        }
    }

    pub(crate) fn affected_places(&self) -> impl Iterator<Item = Place<'tcx>> {
        match self {
            IntroduceConstraints::ExpandForSharedBorrow {
                base_place,
                expansion_places,
                ..
            } => expansion_places
                .iter()
                .chain(std::iter::once(base_place))
                .copied(),
        }
    }
}

pub(crate) struct CapabilityRule<'a, 'tcx> {
    pub(crate) pre: CapabilityConstraint<'a>,
    pub(crate) post: HashMap<Place<'tcx>, CapabilityKind>,
}

impl<'a, 'tcx> CapabilityRule<'a, 'tcx> {
    pub fn new(pre: CapabilityConstraint<'a>, post: HashMap<Place<'tcx>, CapabilityKind>) -> Self {
        Self { pre, post }
    }
}

pub(crate) enum CapabilityRules<'a, 'tcx> {
    OneOf(IndexVec<Decision, CapabilityRule<'a, 'tcx>>),
}

impl<'a, 'tcx> CapabilityRules<'a, 'tcx> {
    pub(crate) fn one_of(rules: Vec<CapabilityRule<'a, 'tcx>>) -> Self {
        Self::OneOf(IndexVec::from_iter(rules))
    }
}

impl<'a, 'tcx> SymbolicCapabilityCtxt<'a, 'tcx> {
    pub(crate) fn require(&self, constraint: CapabilityConstraint<'a>) {
        self.constraints.borrow_mut().0.insert(constraint);
    }

    pub(crate) fn new(arena: PcgArena<'a>) -> Self {
        Self {
            constraints: arena.alloc(RefCell::new(SymbolicCapabilityConstraints(
                HashSet::default(),
            ))),
            vars: arena.alloc(RefCell::new(CapabilityVars(vec![]))),
            choices: arena.alloc(RefCell::new(Choices::new())),
        }
    }

    pub(crate) fn add_choice(&self, choice: Choice) -> ChoiceIdx {
        self.choices.borrow_mut().add_choice(choice)
    }

    pub(crate) fn introduce_var(
        &self,
        place: Place<'tcx>,
        location: SnapshotLocation,
    ) -> CapabilityVar {
        pcg_validity_assert!(
            !self
                .vars
                .borrow()
                .contains(PlaceAtLocation::new(place, location))
        );
        self.vars
            .borrow_mut()
            .insert(PlaceAtLocation::new(place, location))
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, From)]
pub enum SymbolicCapability {
    Concrete(CapabilityKind),
    Variable(CapabilityVar),
}

impl SymbolicCapability {
    pub(crate) fn gte<'a>(self, other: impl Into<Self>) -> CapabilityConstraint<'a> {
        CapabilityConstraint::gte(self, other.into())
    }
}

mod private {
    use crate::pcg::CapabilityKind;

    pub trait CapabilityLike: Copy + PartialEq + From<CapabilityKind> + 'static {
        fn expect_concrete(self) -> CapabilityKind;
        fn minimum<C>(self, other: Self, _ctxt: C) -> Option<Self> {
            self.expect_concrete()
                .minimum(other.expect_concrete())
                .map(|c| c.into())
        }
    }
}

pub(crate) use private::*;

impl CapabilityLike for CapabilityKind {
    fn expect_concrete(self) -> CapabilityKind {
        self
    }
}

impl CapabilityLike for SymbolicCapability {
    fn expect_concrete(self) -> CapabilityKind {
        match self {
            SymbolicCapability::Concrete(c) => c,
            SymbolicCapability::Variable(_) => panic!("Expected concrete capability"),
        }
    }
}

impl SymbolicCapability {
    pub(crate) fn expect_concrete(self) -> CapabilityKind {
        match self {
            SymbolicCapability::Concrete(c) => c,
            other => panic!("Expected concrete capability, got {:?}", other),
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum CapabilityKind {
    /// For borrowed places only: permits reads from the location, but not writes or
    /// drops.
    Read,

    /// For owned places, this capability is used when the place is moved out
    /// of. This capability is used for both owned and borrowed places just before
    /// they are overwritten.
    Write,

    /// Writes and reads are permitted to this place, and the place is not
    /// borrowed.
    Exclusive,

    /// [`CapabilityKind::Exclusive`] for everything not through a dereference,
    /// [`CapabilityKind::Write`] for everything through a dereference.
    ShallowExclusive,
}
impl Debug for CapabilityKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            CapabilityKind::Read => write!(f, "R"),
            CapabilityKind::Write => write!(f, "W"),
            CapabilityKind::Exclusive => write!(f, "E"),
            CapabilityKind::ShallowExclusive => write!(f, "e"),
        }
    }
}

impl PartialOrd for CapabilityKind {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if *self == *other {
            return Some(Ordering::Equal);
        }
        match (*self, *other) {
            // Exclusive is greater than everything below it
            (CapabilityKind::Exclusive, CapabilityKind::ShallowExclusive) => {
                Some(Ordering::Greater)
            }
            (CapabilityKind::ShallowExclusive, CapabilityKind::Exclusive) => Some(Ordering::Less),

            // ShallowExclusive > Write
            (CapabilityKind::ShallowExclusive, CapabilityKind::Write) => Some(Ordering::Greater),
            (CapabilityKind::Write, CapabilityKind::ShallowExclusive) => Some(Ordering::Less),

            // Transitive relationships through ShallowExclusive
            (CapabilityKind::Exclusive, CapabilityKind::Write) => Some(Ordering::Greater),
            (CapabilityKind::Write, CapabilityKind::Exclusive) => Some(Ordering::Less),

            (CapabilityKind::Exclusive, CapabilityKind::Read) => Some(Ordering::Greater),
            (CapabilityKind::Read, CapabilityKind::Exclusive) => Some(Ordering::Less),

            // All other pairs are incomparable
            _ => None,
        }
    }
}

impl CapabilityKind {
    pub fn is_exclusive(self) -> bool {
        matches!(self, CapabilityKind::Exclusive)
    }
    pub fn is_read(self) -> bool {
        matches!(self, CapabilityKind::Read)
    }
    pub fn is_write(self) -> bool {
        matches!(self, CapabilityKind::Write)
    }
    pub fn is_shallow_exclusive(self) -> bool {
        matches!(self, CapabilityKind::ShallowExclusive)
    }

    pub fn minimum(self, other: Self) -> Option<Self> {
        match self.partial_cmp(&other) {
            Some(Ordering::Greater) => Some(other),
            Some(Ordering::Less) => Some(self),
            Some(Ordering::Equal) => Some(self),
            None => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    #[test]
    fn test_capability_gte_macro() {
        // Test that the macro generates correct patterns
        let test_read = |cap: CapabilityKind| -> bool { matches!(cap, capability_gte!(R)) };
        let test_write = |cap: CapabilityKind| -> bool { matches!(cap, capability_gte!(W)) };
        let test_shallow = |cap: CapabilityKind| -> bool { matches!(cap, capability_gte!(e)) };
        let test_exclusive = |cap: CapabilityKind| -> bool { matches!(cap, capability_gte!(E)) };

        // Test Read pattern (should match Read and Exclusive)
        assert!(test_read(CapabilityKind::Read));
        assert!(!test_read(CapabilityKind::Write));
        assert!(!test_read(CapabilityKind::ShallowExclusive));
        assert!(test_read(CapabilityKind::Exclusive));

        // Test Write pattern (should match Write, ShallowExclusive, and Exclusive)
        assert!(!test_write(CapabilityKind::Read));
        assert!(test_write(CapabilityKind::Write));
        assert!(test_write(CapabilityKind::ShallowExclusive));
        assert!(test_write(CapabilityKind::Exclusive));

        // Test ShallowExclusive pattern (should match ShallowExclusive and Exclusive)
        assert!(!test_shallow(CapabilityKind::Read));
        assert!(!test_shallow(CapabilityKind::Write));
        assert!(test_shallow(CapabilityKind::ShallowExclusive));
        assert!(test_shallow(CapabilityKind::Exclusive));

        // Test Exclusive pattern (should match only Exclusive)
        assert!(!test_exclusive(CapabilityKind::Read));
        assert!(!test_exclusive(CapabilityKind::Write));
        assert!(!test_exclusive(CapabilityKind::ShallowExclusive));
        assert!(test_exclusive(CapabilityKind::Exclusive));

        // Also test with full names
        assert!(matches!(CapabilityKind::Read, capability_gte!(Read)));
        assert!(matches!(CapabilityKind::Exclusive, capability_gte!(Read)));
        assert!(matches!(CapabilityKind::Write, capability_gte!(Write)));
        assert!(matches!(
            CapabilityKind::ShallowExclusive,
            capability_gte!(ShallowExclusive)
        ));
    }

    #[test]
    fn test_capability_kind_dag_reachability() {
        use petgraph::algo::has_path_connecting;
        use petgraph::graph::DiGraph;

        // Create directed graph
        let mut graph = DiGraph::new();
        let mut node_indices = HashMap::new();

        let caps = [
            CapabilityKind::Exclusive,
            CapabilityKind::ShallowExclusive,
            CapabilityKind::Write,
            CapabilityKind::Read,
        ];
        // Add nodes
        for cap in caps {
            node_indices.insert(cap, graph.add_node(cap));
        }

        // Add edges (a -> b means a is greater than b)
        let edges = [
            (CapabilityKind::Exclusive, CapabilityKind::ShallowExclusive),
            (CapabilityKind::ShallowExclusive, CapabilityKind::Write),
            (CapabilityKind::Exclusive, CapabilityKind::Read),
        ];

        for (from, to) in edges {
            graph.add_edge(node_indices[&from], node_indices[&to], ());
        }

        // Test that partial_cmp matches graph reachability
        for a in caps {
            for b in caps {
                if a == b {
                    assert!(a.partial_cmp(&b) == Some(Ordering::Equal));
                } else if has_path_connecting(&graph, node_indices[&a], node_indices[&b], None) {
                    assert!(a.partial_cmp(&b) == Some(Ordering::Greater));
                } else if has_path_connecting(&graph, node_indices[&b], node_indices[&a], None) {
                    assert!(a.partial_cmp(&b) == Some(Ordering::Less));
                } else {
                    assert!(a.partial_cmp(&b).is_none());
                }
            }
        }
    }
}
