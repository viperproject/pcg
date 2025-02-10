use std::collections::{BTreeSet, HashSet};

use serde_json::json;

use crate::{
    rustc_interface::middle::mir::{BasicBlock, START_BLOCK},
    utils::PlaceRepacker,
};

use super::domain::ToJsonWithRepacker;

#[derive(Copy, PartialEq, Eq, Clone, Hash, PartialOrd, Ord, Debug)]
pub struct PathCondition {
    pub from: BasicBlock,
    pub to: BasicBlock,
}

impl PathCondition {
    pub fn new(from: BasicBlock, to: BasicBlock) -> Self {
        Self { from, to }
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash, PartialOrd, Ord)]
pub struct Path(Vec<BasicBlock>);

impl Path {
    pub fn new(block: BasicBlock) -> Self {
        Self(vec![block])
    }

    pub fn append(&mut self, block: BasicBlock) {
        self.0.push(block);
    }

    pub fn start(&self) -> BasicBlock {
        self.0[0]
    }

    pub fn end(&self) -> BasicBlock {
        self.0[self.0.len() - 1]
    }
}

#[derive(PartialEq, Eq, Clone, Hash, PartialOrd, Ord, Debug)]
pub struct PCGraph(BTreeSet<PathCondition>);

impl std::fmt::Display for PCGraph {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for pc in self.0.iter() {
            write!(f, "{:?} -> {:?},", pc.from, pc.to)?;
        }
        Ok(())
    }
}

impl PCGraph {
    pub(crate) fn edges_to(&self, block: BasicBlock) -> BTreeSet<PathCondition> {
        self.0
            .iter()
            .filter(|pc| pc.to == block)
            .map(|pc| *pc)
            .collect()
    }

    pub(crate) fn roots(&self) -> HashSet<BasicBlock> {
        self.0
            .iter()
            .filter(|pc| !self.has_path_to_block(pc.from))
            .map(|pc| pc.from)
            .collect()
    }

    pub(crate) fn end(&self) -> Option<BasicBlock> {
        let ends = self
            .0
            .iter()
            .filter(|pc| !self.has_path_from_block(pc.to))
            .map(|pc| pc.to)
            .collect::<Vec<_>>();
        if ends.len() == 1 {
            Some(ends[0])
        } else {
            None
        }
    }

    pub(crate) fn singleton(pc: PathCondition) -> Self {
        Self(BTreeSet::from([pc]))
    }

    pub(crate) fn join(&mut self, other: &Self) -> bool {
        let mut changed = false;
        for pc in other.0.iter() {
            if self.insert(*pc) {
                changed = true;
            }
        }
        changed
    }

    pub(crate) fn has_path_to_block(&self, block: BasicBlock) -> bool {
        self.0.iter().any(|pc| pc.to == block)
    }

    pub(crate) fn has_path_from_block(&self, block: BasicBlock) -> bool {
        self.0.iter().any(|pc| pc.from == block)
    }

    /// Returns `true` iff for any root `bb_r` of the graph, there is a suffix
    /// of `path` [bb_r, ..., bb_l] such that there is a path from `bb_r` to
    /// `bb_l` in the graph.
    pub(crate) fn has_suffix_of(&self, path: &[BasicBlock]) -> bool {
        let check_path = |path: &[BasicBlock]| {
            let mut i = 0;
            while i < path.len() - 1 {
                let f = path[i];
                let t = path[i + 1];
                if !self.0.contains(&PathCondition::new(f, t)) {
                    return false;
                }
                i += 1
            }
            true
        };
        for root in self.roots() {
            let root_idx = path.iter().position(|b| *b == root).unwrap_or(0);
            let path = &path[root_idx..];
            if check_path(path) {
                return true;
            }
        }
        false
    }

    pub(crate) fn insert(&mut self, pc: PathCondition) -> bool {
        self.0.insert(pc)
    }
}

#[derive(PartialEq, Eq, Clone, Hash, PartialOrd, Ord, Debug)]
pub enum PathConditions {
    AtBlock(BasicBlock),
    Paths(PCGraph),
}

impl<'tcx> ToJsonWithRepacker<'tcx> for PathConditions {
    fn to_json(&self, _repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        match self {
            PathConditions::AtBlock(b) => json!({
                "type": "AtBlock",
                "block": format!("{:?}", b)
            }),
            PathConditions::Paths(p) => json!({
                "type": "Paths",
                "paths": p.0.iter().map(|pc| format!("{:?} -> {:?}", pc.from, pc.to)).collect::<Vec<_>>()
            }),
        }
    }
}

impl std::fmt::Display for PathConditions {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PathConditions::AtBlock(b) => write!(f, "{:?}", b),
            PathConditions::Paths(p) => write!(f, "{}", p),
        }
    }
}

impl PathConditions {
    pub fn new(block: BasicBlock) -> Self {
        Self::AtBlock(block)
    }

    pub fn start() -> Self {
        Self::AtBlock(START_BLOCK)
    }

    pub fn roots(&self) -> HashSet<BasicBlock> {
        match self {
            PathConditions::AtBlock(b) => HashSet::from([*b]),
            PathConditions::Paths(p) => p.roots(),
        }
    }

    pub fn end(&self) -> Option<BasicBlock> {
        match self {
            PathConditions::AtBlock(b) => Some(*b),
            PathConditions::Paths(p) => p.end(),
        }
    }

    pub fn join(&mut self, other: &Self) -> bool {
        match (&mut *self, other) {
            (PathConditions::AtBlock(b1), PathConditions::AtBlock(b2)) => {
                assert!(*b1 == *b2);
                false
            }
            (PathConditions::Paths(p1), PathConditions::Paths(p2)) => p1.join(p2),
            (PathConditions::AtBlock(_b), PathConditions::Paths(p)) => {
                *self = PathConditions::Paths(p.clone());
                true
            }
            (PathConditions::Paths(p), PathConditions::AtBlock(_b)) => false,
        }
    }

    pub fn insert(&mut self, pc: PathCondition) -> bool {
        match self {
            PathConditions::AtBlock(b) => {
                assert!(*b == pc.from);
                *self = PathConditions::Paths(PCGraph::singleton(pc));
                true
            }
            PathConditions::Paths(p) => p.insert(pc),
        }
    }

    /// Returns `true` iff for any root `bb_r` of the graph, there is a suffix
    /// of `path` [bb_r, ..., bb_l] such that there is a path from `bb_r` to
    /// `bb_l` in the graph.
    pub fn valid_for_path(&self, path: &[BasicBlock]) -> bool {
        match self {
            PathConditions::AtBlock(b) => path.last() == Some(b),
            PathConditions::Paths(p) => p.has_suffix_of(path),
        }
    }
}
