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
    borrow_edge::BorrowEdge, borrows_graph::Conditioned, deref_expansion::DerefExpansion,
    latest::Latest, region_projection_member::RegionProjectionMember, unblock_graph::UnblockGraph,
};
use combined_pcs::{BodyWithBorrowckFacts, PCGContext, PCGEngine, PlaceCapabilitySummary};
use free_pcs::{CapabilityKind, RepackOp};
use rustc_interface::{data_structures::fx::FxHashSet, dataflow::Analysis, middle::ty::TyCtxt};
use serde_json::json;
use utils::{Place, PlaceRepacker};
use visualization::mir_graph::generate_json_from_mir;

use crate::borrows::domain::ToJsonWithRepacker;

pub type FpcsOutput<'mir, 'tcx> = free_pcs::FreePcsAnalysis<
    'mir,
    'tcx,
    PlaceCapabilitySummary<'mir, 'tcx>,
    PCGEngine<'mir, 'tcx>,
>;
/// Instructs that the current capability to the place (first [`CapabilityKind`]) should
/// be weakened to the second given capability. We guarantee that `_.1 > _.2`.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Weaken<'tcx>(pub Place<'tcx>, pub CapabilityKind, pub CapabilityKind);

/// Instructs that the current capability to the place should be restored to the given capability, e.g.
/// a lent exclusive capability should be restored to an exclusive capability.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct RestoreCapability<'tcx>(pub Place<'tcx>, pub CapabilityKind);

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
    pub added_region_projection_members: FxHashSet<Conditioned<RegionProjectionMember<'tcx>>>,
    pub expands: FxHashSet<Conditioned<DerefExpansion<'tcx>>>,
    pub added_borrows: FxHashSet<Conditioned<BorrowEdge<'tcx>>>,
    pub ug: UnblockGraph<'tcx>,
    pub weakens: FxHashSet<Weaken<'tcx>>,
    pub restores: FxHashSet<RestoreCapability<'tcx>>,
}

impl<'tcx> BorrowsBridge<'tcx> {
    pub fn new() -> BorrowsBridge<'tcx> {
        BorrowsBridge {
            added_region_projection_members: FxHashSet::default(),
            expands: FxHashSet::default(),
            added_borrows: FxHashSet::default(),
            ug: UnblockGraph::new(),
            weakens: FxHashSet::default(),
            restores: FxHashSet::default(),
        }
    }
    pub fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        json!({
            "added_region_projection_members": self.added_region_projection_members.iter().map(|r| r.to_json(repacker)).collect::<Vec<_>>(),
            "expands": self.expands.iter().map(|e| e.to_json(repacker)).collect::<Vec<_>>(),
            "added_borrows": self.added_borrows.iter().map(|r| r.to_json(repacker)).collect::<Vec<_>>(),
            "ug": self.ug.to_json(repacker),
            "weakens": self.weakens.iter().map(|w| w.to_json(repacker)).collect::<Vec<_>>(),
        })
    }
}

use std::sync::Mutex;

lazy_static::lazy_static! {
    /// Whether to record PCG information for each block. This is used for
    /// debugging only. This is set to true when the PCG is initially
    /// constructed, and then disabled after its construction. The reason for
    /// using a global variable is that debugging information is written during
    /// the dataflow operations of the PCG, which are also used when examining
    /// PCG results. We don't want to write the debugging information to disk
    /// during examination, of course.
    static ref RECORD_PCG: Mutex<bool> = Mutex::new(false);
}

struct PCGStmtVisualizationData<'a, 'tcx> {
    /// The value of the "latest" map at the end of the statement.
    latest: &'a Latest<'tcx>,
    free_pcg_repacks_start: &'a Vec<RepackOp<'tcx>>,
    free_pcg_repacks_middle: &'a Vec<RepackOp<'tcx>>,
    borrows_bridge_start: &'a BorrowsBridge<'tcx>,
    borrows_bridge_middle: &'a BorrowsBridge<'tcx>,
}

impl<'a, 'tcx> ToJsonWithRepacker<'tcx> for PCGStmtVisualizationData<'a, 'tcx> {
    fn to_json(&self, repacker: PlaceRepacker<'_, 'tcx>) -> serde_json::Value {
        json!({
            "latest": self.latest.to_json(repacker),
            "free_pcg_repacks_start": self.free_pcg_repacks_start.iter().map(|r| r.to_json()).collect::<Vec<_>>(),
            "free_pcg_repacks_middle": self.free_pcg_repacks_middle.iter().map(|r| r.to_json()).collect::<Vec<_>>(),
            "borrows_bridge_start": self.borrows_bridge_start.to_json(repacker),
            "borrows_bridge_middle": self.borrows_bridge_middle.to_json(repacker),
        })
    }
}

pub fn run_combined_pcs<'mir, 'tcx>(
    mir: &'mir BodyWithBorrowckFacts<'tcx>,
    tcx: TyCtxt<'tcx>,
    visualization_output_path: Option<String>,
) -> FpcsOutput<'mir, 'tcx> {
    let cgx = PCGContext::new(tcx, mir);
    let fpcg = PCGEngine::new(cgx, visualization_output_path.clone());
    {
        let mut record_pcs = RECORD_PCG.lock().unwrap();
        *record_pcs = true;
    }
    let analysis = fpcg
        .into_engine(tcx, &mir.body)
        .pass_name("free_pcg")
        .iterate_to_fixpoint();
    {
        let mut record_pcg = RECORD_PCG.lock().unwrap();
        *record_pcg = false;
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
        let edge_legend_file_path = format!("{}/edge_legend.dot", dir_path);
        let edge_legend_graph = crate::visualization::legend::generate_edge_legend().unwrap();
        std::fs::write(&edge_legend_file_path, edge_legend_graph)
            .expect("Failed to write edge legend");

        let node_legend_file_path = format!("{}/node_legend.dot", dir_path);
        let node_legend_graph = crate::visualization::legend::generate_node_legend().unwrap();
        std::fs::write(&node_legend_file_path, node_legend_graph)
            .expect("Failed to write node legend");
        generate_json_from_mir(&format!("{}/mir.json", dir_path), tcx, &mir.body)
            .expect("Failed to generate JSON from MIR");

        let rp = PCGContext::new(tcx, mir).rp;

        // Iterate over each statement in the MIR
        for (block, _data) in mir.body.basic_blocks.iter_enumerated() {
            let pcs_block = fpcs_analysis.get_all_for_bb(block);
            for (statement_index, statement) in pcs_block.statements.iter().enumerate() {
                let data = PCGStmtVisualizationData {
                    latest: &statement.borrows.post_main.latest,
                    free_pcg_repacks_start: &statement.repacks_start,
                    free_pcg_repacks_middle: &statement.repacks_middle,
                    borrows_bridge_start: &statement.extra_start,
                    borrows_bridge_middle: &statement.extra_middle,
                };
                let pcg_data_file_path = format!(
                    "{}/block_{}_stmt_{}_pcg_data.json",
                    &dir_path,
                    block.index(),
                    statement_index
                );
                let pcg_data_json = data.to_json(rp);
                std::fs::write(&pcg_data_file_path, pcg_data_json.to_string())
                    .expect("Failed to write pcg data to JSON file");
            }
        }
    }

    fpcs_analysis
}
