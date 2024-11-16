// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![feature(rustc_private)]
#![feature(box_patterns, hash_extract_if, extract_if)]
#![feature(if_let_guard, let_chains)]

pub mod borrows;
pub mod combined_pcs;
pub mod coupling;
pub mod free_pcs;
pub mod r#loop;
pub mod rustc_interface;
pub mod utils;
pub mod visualization;

use borrows::{
    borrow_edge::BorrowEdge, borrows_graph::Conditioned,
    deref_expansion::DerefExpansion, unblock_graph::UnblockGraph,
};
use combined_pcs::{BodyWithBorrowckFacts, PcsContext, PcsEngine, PlaceCapabilitySummary};
use free_pcs::CapabilityKind;
use rustc_interface::{
    data_structures::fx::FxHashSet,
    dataflow::Analysis,
    middle::ty::TyCtxt,
};
use serde_json::json;
use utils::{Place, PlaceRepacker};
use visualization::mir_graph::generate_json_from_mir;

use crate::borrows::domain::ToJsonWithRepacker;

pub type FpcsOutput<'mir, 'tcx> = free_pcs::FreePcsAnalysis<
    'mir,
    'tcx,
    PlaceCapabilitySummary<'mir, 'tcx>,
    PcsEngine<'mir, 'tcx>,
>;

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Weaken<'tcx>(Place<'tcx>, CapabilityKind, CapabilityKind);

impl<'tcx> ToJsonWithRepacker<'tcx> for Weaken<'tcx> {
    fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        json!({
            "place": self.0.to_json(repacker),
            "old": format!("{:?}", self.1),
            "new": format!("{:?}", self.2),
        })
    }
}

#[derive(Clone, Debug)]
pub struct BorrowsBridge<'tcx> {
    pub expands: FxHashSet<Conditioned<DerefExpansion<'tcx>>>,
    pub added_borrows: FxHashSet<Conditioned<BorrowEdge<'tcx>>>,
    pub ug: UnblockGraph<'tcx>,
    pub weakens: FxHashSet<Weaken<'tcx>>,
}

impl<'tcx> BorrowsBridge<'tcx> {
    pub fn new() -> BorrowsBridge<'tcx> {
        BorrowsBridge {
            expands: FxHashSet::default(),
            added_borrows: FxHashSet::default(),
            ug: UnblockGraph::new(),
            weakens: FxHashSet::default(),
        }
    }
    pub fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        json!({
            "expands": self.expands.iter().map(|e| e.to_json(repacker)).collect::<Vec<_>>(),
            "added_borrows": self.added_borrows.iter().map(|r| r.to_json(repacker)).collect::<Vec<_>>(),
            "ug": self.ug.to_json(repacker),
            "weakens": self.weakens.iter().map(|w| w.to_json(repacker)).collect::<Vec<_>>(),
        })
    }
}

use std::sync::Mutex;

lazy_static::lazy_static! {
    static ref RECORD_PCS: Mutex<bool> = Mutex::new(false);
}

pub fn run_combined_pcs<'mir, 'tcx>(
    mir: &'mir BodyWithBorrowckFacts<'tcx>,
    tcx: TyCtxt<'tcx>,
    visualization_output_path: Option<String>,
) -> FpcsOutput<'mir, 'tcx> {
    let cgx = PcsContext::new(tcx, mir);
    let fpcs = PcsEngine::new(cgx, visualization_output_path.clone());
    {
        let mut record_pcs = RECORD_PCS.lock().unwrap();
        *record_pcs = true;
    }
    let analysis = fpcs
        .into_engine(tcx, &mir.body)
        .pass_name("free_pcs")
        .iterate_to_fixpoint();
    {
        let mut record_pcs = RECORD_PCS.lock().unwrap();
        *record_pcs = false;
    }
    if let Some(dir_path) = &visualization_output_path {
        for block in mir.body.basic_blocks.indices() {
            let state = analysis.entry_set_for_block(block);
            assert!(state.block() == block);
            let block_iterations_json_file =
                format!("{}/block_{}_iterations.json", dir_path, block.index());
            state
                .dot_graphs()
                .borrow()
                .write_json_file(&block_iterations_json_file);
        }
    }
    let mut fpcs_analysis = free_pcs::FreePcsAnalysis::new(analysis.into_results_cursor(&mir.body));

    if let Some(dir_path) = visualization_output_path {
        generate_json_from_mir(&format!("{}/mir.json", dir_path), tcx, &mir.body)
            .expect("Failed to generate JSON from MIR");

        let rp = PcsContext::new(tcx, mir).rp;

        // Iterate over each statement in the MIR
        for (block, _data) in mir.body.basic_blocks.iter_enumerated() {
            let pcs_block = fpcs_analysis.get_all_for_bb(block);
            for (statement_index, statement) in pcs_block.statements.iter().enumerate() {
                let borrows_file_path = format!(
                    "{}/block_{}_stmt_{}_borrows.json",
                    &dir_path,
                    block.index(),
                    statement_index
                );
                let borrows_json =
                    serde_json::to_string_pretty(&statement.borrows.to_json(rp)).unwrap();
                std::fs::write(&borrows_file_path, borrows_json)
                    .expect("Failed to write borrows to JSON file");
            }
        }
    }

    fpcs_analysis
}
