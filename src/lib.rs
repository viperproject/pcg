// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![feature(associated_type_defaults)]
#![feature(rustc_private)]
#![feature(box_patterns)]
#![feature(if_let_guard, let_chains)]
#![feature(never_type)]
#![feature(proc_macro_hygiene)]
#![feature(anonymous_lifetime_in_impl_trait)]
#![feature(stmt_expr_attributes)]
#![feature(allocator_api)]
pub mod action;
pub mod borrow_checker;
pub mod borrow_pcg;
pub mod free_pcs;
pub mod r#loop;
pub mod pcg;
pub mod rustc_interface;
pub mod utils;
pub mod visualization;

use action::PcgActions;
use borrow_checker::BorrowCheckerInterface;
use borrow_pcg::{graph::borrows_imgcat_debug, latest::Latest};
use free_pcs::{CapabilityKind, PcgLocation};
use pcg::{EvalStmtPhase, PcgEngine, PcgSuccessor};
use rustc_interface::{
    borrowck::{self, BorrowSet, LocationTable, PoloniusInput, RegionInferenceContext},
    dataflow::{compute_fixpoint, AnalysisEngine},
    middle::{
        mir::Body,
        ty::{self, TyCtxt},
    },
    mir_dataflow::move_paths::MoveData,
};
use serde_json::json;
use utils::{
    display::{DebugLines, DisplayWithCompilerCtxt},
    validity::HasValidityCheck,
    CompilerCtxt, Place, VALIDITY_CHECKS, VALIDITY_CHECKS_WARN_ONLY,
};
use visualization::mir_graph::generate_json_from_mir;

use utils::json::ToJsonWithCompilerCtxt;

pub(crate) mod private {
    #[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
    pub enum WeakenReason {
        RefBorrowExpired,
        RefTwoPhaseBorrowActivated,
        Other,
    }
}

/// The result of the PCG analysis.
pub type PcgOutput<'mir, 'tcx, A> = free_pcs::PcgAnalysis<'mir, 'tcx, A>;
/// Instructs that the current capability to the place (first [`CapabilityKind`]) should
/// be weakened to the second given capability. We guarantee that `_.1 > _.2`.
/// If `_.2` is `None`, the capability is removed.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct Weaken<'tcx> {
    pub(crate) place: Place<'tcx>,
    pub(crate) from: CapabilityKind,
    pub(crate) to: Option<CapabilityKind>,
    pub(crate) reason: private::WeakenReason,
}

impl<'tcx> Weaken<'tcx> {
    pub(crate) fn debug_line<BC: Copy>(&self, ctxt: CompilerCtxt<'_, 'tcx, BC>) -> String {
        let to_str = match self.to {
            Some(to) => format!("{to:?}"),
            None => "None".to_string(),
        };
        format!(
            "Weaken {} from {:?} to {}",
            self.place.to_short_string(ctxt),
            self.from,
            to_str
        )
    }

    pub(crate) fn new(
        place: Place<'tcx>,
        from: CapabilityKind,
        to: Option<CapabilityKind>,
        reason: private::WeakenReason,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Self {
        // TODO: Sometimes R can be downgraded to W
        if validity_checks_enabled() {
            match reason {
                private::WeakenReason::RefBorrowExpired
                | private::WeakenReason::RefTwoPhaseBorrowActivated => {
                    pcg_validity_assert!(
                        place.is_ref(ctxt),
                        "Place {} is not a ref",
                        place.to_short_string(ctxt),
                    );
                    pcg_validity_assert!(
                        to == Some(CapabilityKind::Write),
                        "Unexpected write capability for place {} after ref borrow expired: {:?}",
                        place.to_short_string(ctxt),
                        to
                    );
                }
                _ => {
                    if let Some(to) = to {
                        pcg_validity_assert!(
                from > to,
                "Weak of ({}: {}): FROM capability ({:?}) is not greater than TO capability ({:?})",
                place.to_short_string(ctxt),
                place.ty(ctxt).ty,
                from, to);
                    }
                }
            }
        }
        Self {
            place,
            from,
            to,
            reason,
        }
    }

    pub fn place(&self) -> Place<'tcx> {
        self.place
    }

    pub fn from_cap(&self) -> CapabilityKind {
        self.from
    }

    pub fn to_cap(&self) -> Option<CapabilityKind> {
        self.to
    }
}

/// Instructs that the capability to the place should be restored to the
/// given capability, e.g. after a borrow expires, the borrowed place should be
/// restored to exclusive capability.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct RestoreCapability<'tcx> {
    place: Place<'tcx>,
    capability: CapabilityKind,
}

impl<'tcx, BC: Copy> ToJsonWithCompilerCtxt<'tcx, BC> for RestoreCapability<'tcx> {
    fn to_json(&self, ctxt: CompilerCtxt<'_, 'tcx, BC>) -> serde_json::Value {
        json!({
            "place": self.place.to_json(ctxt),
            "capability": format!("{:?}", self.capability),
        })
    }
}
impl<'tcx> RestoreCapability<'tcx> {
    pub(crate) fn debug_line<BC: Copy>(&self, repacker: CompilerCtxt<'_, 'tcx, BC>) -> String {
        format!(
            "Restore {} to {:?}",
            self.place.to_short_string(repacker),
            self.capability,
        )
    }

    pub(crate) fn new(place: Place<'tcx>, capability: CapabilityKind) -> Self {
        Self { place, capability }
    }

    pub fn place(&self) -> Place<'tcx> {
        self.place
    }

    pub fn capability(&self) -> CapabilityKind {
        self.capability
    }
}

impl<'tcx, BC: Copy> ToJsonWithCompilerCtxt<'tcx, BC> for Weaken<'tcx> {
    fn to_json(&self, repacker: CompilerCtxt<'_, 'tcx, BC>) -> serde_json::Value {
        json!({
            "place": self.place.to_json(repacker),
            "old": format!("{:?}", self.from),
            "new": format!("{:?}", self.to),
        })
    }
}

impl<'tcx> DebugLines<CompilerCtxt<'_, 'tcx>> for BorrowPcgActions<'tcx> {
    fn debug_lines(&self, repacker: CompilerCtxt<'_, 'tcx>) -> Vec<String> {
        self.0
            .iter()
            .map(|action| action.debug_line(repacker))
            .collect()
    }
}

use borrow_pcg::action::actions::BorrowPcgActions;
use std::{alloc::Allocator, sync::Mutex};
use utils::eval_stmt_data::EvalStmtData;

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
    actions: &'a EvalStmtData<PcgActions<'tcx>>,
}

struct PcgSuccessorVisualizationData<'a, 'tcx> {
    actions: &'a PcgActions<'tcx>,
}

impl<'tcx, 'a> From<&'a PcgSuccessor<'tcx>> for PcgSuccessorVisualizationData<'a, 'tcx> {
    fn from(successor: &'a PcgSuccessor<'tcx>) -> Self {
        Self {
            actions: &successor.actions,
        }
    }
}

impl<'tcx, 'a> ToJsonWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>
    for PcgSuccessorVisualizationData<'a, 'tcx>
{
    fn to_json(&self, repacker: CompilerCtxt<'_, 'tcx>) -> serde_json::Value {
        json!({
            "actions": self.actions.iter().map(|a| a.to_json(repacker)).collect::<Vec<_>>(),
        })
    }
}

impl<'tcx, 'a> ToJsonWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>
    for PCGStmtVisualizationData<'a, 'tcx>
{
    fn to_json(
        &self,
        repacker: CompilerCtxt<'_, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    ) -> serde_json::Value {
        json!({
            "latest": self.latest.to_json(repacker),
            "actions": self.actions.to_json(repacker),
        })
    }
}

impl<'a, 'tcx> PCGStmtVisualizationData<'a, 'tcx> {
    fn new<'mir>(location: &'a PcgLocation<'tcx>) -> Self
    where
        'tcx: 'mir,
    {
        Self {
            latest: &location.states[EvalStmtPhase::PostMain].borrow.latest,
            actions: &location.actions,
        }
    }
}

/// Exposes accessors to the body and borrow-checker data for a MIR function.
/// Types that implement this trait are used as inputs to the PCG.
///
/// Note that [`borrowck::BodyWithBorrowckFacts`] from the Rust compiler implements this trait.
pub trait BodyAndBorrows<'tcx> {
    fn body(&self) -> &Body<'tcx>;
    fn borrow_set(&self) -> &BorrowSet<'tcx>;
    fn region_inference_context(&self) -> &RegionInferenceContext<'tcx>;
    fn location_table(&self) -> &LocationTable;
    fn input_facts(&self) -> &PoloniusInput;
}

impl<'tcx> BodyAndBorrows<'tcx> for borrowck::BodyWithBorrowckFacts<'tcx> {
    fn body(&self) -> &Body<'tcx> {
        &self.body
    }
    fn borrow_set(&self) -> &BorrowSet<'tcx> {
        &self.borrow_set
    }
    fn region_inference_context(&self) -> &RegionInferenceContext<'tcx> {
        &self.region_inference_context
    }

    fn location_table(&self) -> &LocationTable {
        self.location_table.as_ref().unwrap()
    }

    fn input_facts(&self) -> &PoloniusInput {
        self.input_facts.as_ref().unwrap()
    }
}

pub struct PcgCtxt<'mir, 'tcx> {
    compiler_ctxt: CompilerCtxt<'mir, 'tcx>,
    move_data: MoveData<'tcx>,
}

#[rustversion::since(2024-10-17)]
fn gather_moves<'tcx>(body: &Body<'tcx>, tcx: ty::TyCtxt<'tcx>) -> MoveData<'tcx> {
    MoveData::gather_moves(body, tcx, |_| true)
}

#[rustversion::before(2024-10-17)]
fn gather_moves<'tcx>(body: &Body<'tcx>, tcx: TyCtxt<'tcx>) -> MoveData<'tcx> {
    MoveData::gather_moves(body, tcx, ty::ParamEnv::empty(), |_| true)
}

impl<'mir, 'tcx> PcgCtxt<'mir, 'tcx> {
    pub fn new<BC: BorrowCheckerInterface<'tcx> + ?Sized>(
        body: &'mir Body<'tcx>,
        tcx: TyCtxt<'tcx>,
        bc: &'mir BC,
    ) -> Self {
        let ctxt = CompilerCtxt::new(body, tcx, bc.as_dyn());
        Self {
            compiler_ctxt: ctxt,
            move_data: gather_moves(ctxt.body(), ctxt.tcx()),
        }
    }
}

/// The main entrypoint for running the PCG.
///
/// # Arguments
///
/// - `body`: The body of the MIR function to analyze.
/// - `tcx`: The type context of the MIR function.
/// - `bc`: The borrow-checker that the PCG should use.
/// - `arena`: The arena to use for allocation. You can use [`std::alloc::Global`] if you don't
///   care to use a custom allocator.
/// - `visualization_output_path`: The path to output debug visualization to.
pub fn run_pcg<'a, 'tcx, A: Allocator + Copy + std::fmt::Debug>(
    pcg_ctxt: &'a PcgCtxt<'_, 'tcx>,
    arena: A,
    visualization_output_path: Option<&str>,
) -> PcgOutput<'a, 'tcx, A> {
    let engine = PcgEngine::new(
        pcg_ctxt.compiler_ctxt,
        &pcg_ctxt.move_data,
        arena,
        visualization_output_path,
    );
    {
        let mut record_pcg = RECORD_PCG.lock().unwrap();
        *record_pcg = true;
    }
    let body = pcg_ctxt.compiler_ctxt.body();
    let tcx = pcg_ctxt.compiler_ctxt.tcx();
    let analysis = compute_fixpoint(AnalysisEngine(engine), tcx, body);
    {
        let mut record_pcg = RECORD_PCG.lock().unwrap();
        *record_pcg = false;
    }
    if let Some(dir_path) = &visualization_output_path {
        for block in body.basic_blocks.indices() {
            let state = analysis.entry_set_for_block(block);
            assert!(state.block() == block);
            let block_iterations_json_file =
                format!("{}/block_{}_iterations.json", dir_path, block.index());
            state
                .dot_graphs()
                .unwrap()
                .borrow()
                .write_json_file(&block_iterations_json_file);
        }
    }
    let mut fpcs_analysis = free_pcs::PcgAnalysis::new(analysis.into_results_cursor(body));

    if let Some(dir_path) = visualization_output_path {
        let edge_legend_file_path = format!("{dir_path}/edge_legend.dot");
        let edge_legend_graph = crate::visualization::legend::generate_edge_legend().unwrap();
        std::fs::write(&edge_legend_file_path, edge_legend_graph)
            .expect("Failed to write edge legend");

        let node_legend_file_path = format!("{dir_path}/node_legend.dot");
        let node_legend_graph = crate::visualization::legend::generate_node_legend().unwrap();
        std::fs::write(&node_legend_file_path, node_legend_graph)
            .expect("Failed to write node legend");
        generate_json_from_mir(&format!("{dir_path}/mir.json"), pcg_ctxt.compiler_ctxt)
            .expect("Failed to generate JSON from MIR");

        // Iterate over each statement in the MIR
        for (block, _data) in body.basic_blocks.iter_enumerated() {
            let pcs_block_option = if let Ok(opt) = fpcs_analysis.get_all_for_bb(block) {
                opt
            } else {
                continue;
            };
            if pcs_block_option.is_none() {
                continue;
            }
            let pcs_block = pcs_block_option.unwrap();
            for (statement_index, statement) in pcs_block.statements.iter().enumerate() {
                if validity_checks_enabled() {
                    statement.assert_validity(pcg_ctxt.compiler_ctxt);
                }
                let data = PCGStmtVisualizationData::new(statement);
                let pcg_data_file_path = format!(
                    "{}/block_{}_stmt_{}_pcg_data.json",
                    &dir_path,
                    block.index(),
                    statement_index
                );
                let pcg_data_json = data.to_json(pcg_ctxt.compiler_ctxt);
                std::fs::write(&pcg_data_file_path, pcg_data_json.to_string())
                    .expect("Failed to write pcg data to JSON file");
            }
            for succ in pcs_block.terminator.succs {
                let data = PcgSuccessorVisualizationData::from(&succ);
                let pcg_data_file_path = format!(
                    "{}/block_{}_term_block_{}_pcg_data.json",
                    &dir_path,
                    block.index(),
                    succ.block().index()
                );
                let pcg_data_json = data.to_json(pcg_ctxt.compiler_ctxt);
                std::fs::write(&pcg_data_file_path, pcg_data_json.to_string())
                    .expect("Failed to write pcg data to JSON file");
            }
        }
    }

    fpcs_analysis
}

macro_rules! pcg_validity_assert {
    ($cond:expr) => {
        if $crate::validity_checks_enabled() {
            if $crate::validity_checks_warn_only() {
                #[allow(clippy::neg_cmp_op_on_partial_ord)]
                if !$cond {
                    tracing::error!("assertion failed: {}", stringify!($cond));
                }
            } else {
                #[allow(clippy::neg_cmp_op_on_partial_ord)]
                if !$cond {
                    tracing::error!("assertion failed: {}", stringify!($cond));
                }
                assert!($cond);
            }
        }
    };
    ($cond:expr, $($arg:tt)*) => {
        if $crate::validity_checks_enabled() {
            if $crate::validity_checks_warn_only() {
                #[allow(clippy::neg_cmp_op_on_partial_ord)]
                if !$cond {
                    tracing::error!($($arg)*);
                }
            } else {
                #[allow(clippy::neg_cmp_op_on_partial_ord)]

                if !$cond {
                    tracing::error!($($arg)*);
                }
                assert!($cond, $($arg)*);
            }
        }
    };
}

pub(crate) use pcg_validity_assert;

pub(crate) fn validity_checks_enabled() -> bool {
    *VALIDITY_CHECKS
}

pub(crate) fn validity_checks_warn_only() -> bool {
    *VALIDITY_CHECKS_WARN_ONLY
}
