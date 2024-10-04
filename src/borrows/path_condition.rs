use std::collections::BTreeSet;

use serde_json::json;

use crate::{
    rustc_interface::middle::mir::{BasicBlock, BasicBlocks},
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
    pub fn root(&self) -> Option<BasicBlock> {
        self.0
            .iter()
            .find(|pc| !self.has_path_to_block(pc.from))
            .map(|pc| pc.from)
    }

    pub fn end(&self) -> Option<BasicBlock> {
        self.0
            .iter()
            .find(|pc| !self.has_path_from_block(pc.to))
            .map(|pc| pc.to)
    }

    pub fn singleton(pc: PathCondition) -> Self {
        Self(BTreeSet::from([pc]))
    }

    pub fn join(&mut self, other: &Self) -> bool {
        let mut changed = false;
        for pc in other.0.iter() {
            if self.insert(*pc) {
                changed = true;
            }
        }
        changed
    }

    pub fn has_path_to_block(&self, block: BasicBlock) -> bool {
        self.0.iter().any(|pc| pc.to == block)
    }

    pub fn has_path_from_block(&self, block: BasicBlock) -> bool {
        self.0.iter().any(|pc| pc.from == block)
    }

    pub fn has_suffix_of(&self, path: &[BasicBlock]) -> bool {
        let path = if let Some(root) = self.root() {
            let root_idx = path.iter().position(|b| *b == root).unwrap_or(0);
            &path[root_idx..]
        } else {
            path
        };
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
    }

    pub fn insert(&mut self, pc: PathCondition) -> bool {
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

    pub fn root(&self) -> Option<BasicBlock> {
        match self {
            PathConditions::AtBlock(b) => Some(*b),
            PathConditions::Paths(p) => p.root(),
        }
    }

    pub fn end(&self) -> Option<BasicBlock> {
        match self {
            PathConditions::AtBlock(b) => Some(*b),
            PathConditions::Paths(p) => p.end(),
        }
    }

    /// Returns true if no path through the program would satisfy both conditions.
    pub fn mutually_exclusive(&self, other: &Self, blocks: &BasicBlocks<'_>) -> bool {
        if self == other {
            return false;
        }
        match (self.root(), other.root(), self.end(), other.end()) {
            (Some(r1), Some(r2), Some(e1), Some(e2)) => {
                let preds = blocks.predecessors();
                !preds[r1].contains(&e2) && !preds[r2].contains(&e1)
            }
            _ => false,
        }
    }

    pub fn join(&mut self, other: &Self) -> bool {
        match (self, other) {
            (PathConditions::AtBlock(b1), PathConditions::AtBlock(b2)) => {
                assert!(*b1 == *b2);
                false
            }
            (PathConditions::Paths(p1), PathConditions::Paths(p2)) => p1.join(p2),
            (PathConditions::AtBlock(_b), PathConditions::Paths(_p)) => false, // TODO: check
            (PathConditions::Paths(_p), PathConditions::AtBlock(_b)) => false, // TODO: check
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

    pub fn valid_for_path(&self, path: &[BasicBlock]) -> bool {
        match self {
            PathConditions::AtBlock(b) => path.last() == Some(b),
            PathConditions::Paths(p) => p.has_suffix_of(path),
        }
    }
}
