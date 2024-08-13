use std::collections::BTreeSet;

use serde_json::json;

use crate::{rustc_interface::middle::mir::BasicBlock, utils::PlaceRepacker};

use super::domain::ToJsonWithRepacker;

#[derive(PartialEq, Eq, Clone, Hash, PartialOrd, Ord, Debug)]
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
    pub fn root(&self) -> BasicBlock {
        self.0
            .iter()
            .find(|pc| !self.has_path_to_block(pc.from))
            .unwrap()
            .from
    }

    pub fn singleton(pc: PathCondition) -> Self {
        Self(BTreeSet::from([pc]))
    }

    pub fn has_path_to_block(&self, block: BasicBlock) -> bool {
        self.0.iter().any(|pc| pc.to == block)
    }

    pub fn has_suffix_of(&self, path: &[BasicBlock]) -> bool {
        let root_idx = path.iter().position(|b| self.root() == *b);
        match root_idx {
            Some(root_idx) => {
                let path = &path[root_idx..];
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
            None => false,
        }
    }

    pub fn insert(&mut self, pc: PathCondition) -> bool {
        if self.has_path_to_block(pc.from) {
            self.0.insert(pc)
        } else {
            false
        }
    }
}

#[derive(PartialEq, Eq, Clone, Hash, PartialOrd, Ord, Debug)]
pub enum PathConditions {
    AtBlock(BasicBlock),
    Paths(PCGraph),
}

impl<'tcx> ToJsonWithRepacker<'tcx> for PathConditions {
    fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
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

    pub fn insert(&mut self, pc: PathCondition) -> bool {
        match self {
            PathConditions::AtBlock(b) => {
                if *b == pc.from {
                    *self = PathConditions::Paths(PCGraph::singleton(pc));
                    true
                } else {
                    eprintln!("Ignore {:?} for {:?}", pc, b);
                    false
                }
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