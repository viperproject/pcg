use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet},
    fs::File,
    io::Write,
};

use bumpalo::Bump;
use derive_more::From;
use tracing::info;

use crate::{
    borrow_checker::{
        r#impl::{BorrowCheckerImpl, PoloniusBorrowChecker},
        BorrowCheckerInterface,
    },
    borrow_pcg::region_projection::{LocalRegionProjection, PcgRegion, RegionIdx},
    free_pcs::PcgAnalysis,
    pcg::{self, BodyWithBorrowckFacts},
    run_pcg,
    rustc_interface::{
        borrowck::{self, BorrowIndex, LocationTable, RichLocation},
        data_structures::fx::{FxHashMap, FxHashSet},
        driver::{self, Compilation, init_rustc_env_logger},
        hir::{def::DefKind, def_id::LocalDefId},
        interface::{interface::Compiler, Config},
        middle::{
            mir::{Body, Local, Location},
            query::queries::mir_borrowck::ProvidedValue as MirBorrowck,
            ty::{RegionVid, TyCtxt},
            util::Providers,
        },
        session::{Session, EarlyDiagCtxt, config::ErrorOutputType},
        span::SpanSnippetError,
    },
    utils::MAX_BASIC_BLOCKS,
    PcgOutput,
};

#[rustversion::before(2024-11-09)]
use crate::rustc_interface::interface::Queries;

#[cfg(feature = "visualization")]
use crate::visualization::bc_facts_graph::{
    region_inference_outlives, subset_anywhere, subset_at_location, RegionPrettyPrinter,
};

use super::{env_feature_enabled, CompilerCtxt, Place};

pub struct PcgCallbacks;

pub(crate) fn set_mir_borrowck(_session: &Session, providers: &mut Providers) {
    providers.mir_borrowck = mir_borrowck;
}

impl driver::Callbacks for PcgCallbacks {
    fn config(&mut self, config: &mut Config) {
        tracing::debug!("Setting mir_borrowck");
        assert!(config.override_queries.is_none());
        config.override_queries = Some(set_mir_borrowck);
        let early_dcx = EarlyDiagCtxt::new(ErrorOutputType::default());
        init_rustc_env_logger(&early_dcx);
    }

    #[rustversion::before(2024-11-09)]
    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        queries.global_ctxt().unwrap().enter(|tcx| {
            // SAFETY: `config()` overrides the borrowck query to save the bodies
            // from `tcx` in `BODIES`
            unsafe { run_pcg_on_all_fns(tcx, env_feature_enabled("PCG_POLONIUS").unwrap_or(false)) }
        });
        if in_cargo_crate() {
            Compilation::Continue
        } else {
            Compilation::Stop
        }
    }

    #[rustversion::since(2024-11-09)]
    fn after_analysis(&mut self, _compiler: &Compiler, tcx: TyCtxt<'_>) -> Compilation {
        // SAFETY: `config()` overrides the borrowck query to save the bodies
        // from `tcx` in `BODIES`
        unsafe {
            run_pcg_on_all_fns(tcx, env_feature_enabled("PCG_POLONIUS").unwrap_or(false));
        }
        if in_cargo_crate() {
            Compilation::Continue
        } else {
            Compilation::Stop
        }
    }
}

thread_local! {
    pub static BODIES:
        RefCell<FxHashMap<LocalDefId, BodyWithBorrowckFacts<'static>>> =
        RefCell::new(FxHashMap::default());
}

pub(crate) fn mir_borrowck<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> MirBorrowck<'tcx> {
    let consumer_opts = borrowck::ConsumerOptions::PoloniusInputFacts;
    tracing::debug!(
        "Start mir_borrowck for {}",
        tcx.def_path_str(def_id.to_def_id())
    );
    let body_with_facts = borrowck::get_body_with_borrowck_facts(tcx, def_id, consumer_opts);
    tracing::debug!(
        "End mir_borrowck for {}",
        tcx.def_path_str(def_id.to_def_id())
    );
    unsafe {
        let body: BodyWithBorrowckFacts<'tcx> = body_with_facts.into();
        let body: BodyWithBorrowckFacts<'static> = std::mem::transmute(body);
        BODIES.with(|state| {
            let mut map = state.borrow_mut();
            tracing::debug!(
                "Inserting body for {}",
                tcx.def_path_str(def_id.to_def_id())
            );
            assert!(map.insert(def_id, body).is_none());
        });
    }
    let mut providers = Providers::default();
    borrowck::provide(&mut providers);
    let original_mir_borrowck = providers.mir_borrowck;
    original_mir_borrowck(tcx, def_id)
}

fn cargo_crate_name() -> Option<String> {
    std::env::var("CARGO_CRATE_NAME").ok()
}

pub fn in_cargo_crate() -> bool {
    cargo_crate_name().is_some()
}

#[rustversion::before(2025-03-02)]
fn hir_body_owners(tcx: TyCtxt<'_>) -> impl std::iter::Iterator<Item = LocalDefId> + '_ {
    tcx.hir().body_owners()
}

#[rustversion::since(2025-03-02)]
fn hir_body_owners(tcx: TyCtxt<'_>) -> impl std::iter::Iterator<Item = LocalDefId> + '_ {
    tcx.hir_body_owners()
}

/// # Safety
/// The originally saved body must come from the same `tcx`
pub(crate) unsafe fn take_stored_body(
    tcx: TyCtxt<'_>,
    def_id: LocalDefId,
) -> BodyWithBorrowckFacts<'_> {
    BODIES.with(|state| {
        let mut map = state.borrow_mut();
        // SAFETY: The originally saved body comes from the same `tcx`
        unsafe {
            std::mem::transmute(map.remove(&def_id).unwrap_or_else(|| {
                panic!("No body found for {}", tcx.def_path_str(def_id.to_def_id()))
            }))
        }
    })
}

fn should_check_body(body: &Body<'_>) -> bool {
    if let Some(len) = *MAX_BASIC_BLOCKS {
        body.basic_blocks.len() <= len
    } else {
        true
    }
}

fn is_primary_crate() -> bool {
    std::env::var("CARGO_PRIMARY_PACKAGE").is_ok()
}

/// # Safety
///
/// Functions bodies stored in `BODIES` must come from the same `tcx`.
pub(crate) unsafe fn run_pcg_on_all_fns(tcx: TyCtxt<'_>, polonius: bool) {
    tracing::info!("Running PCG on all functions");
    if in_cargo_crate() && !is_primary_crate() {
        // We're running in cargo, but not compiling the primary package
        // We don't want to check dependencies, so abort
        return;
    }

    if std::env::var("PCG_TYPECHECK_ONLY")
        .unwrap_or("false".to_string())
        .parse::<bool>()
        .unwrap()
    {
        return;
    }

    let mut item_names = vec![];

    let user_specified_vis_dir = std::env::var("PCG_VISUALIZATION_DATA_DIR");
    let vis_dir: Option<&str> = if env_feature_enabled("PCG_VISUALIZATION").unwrap_or(false) {
        Some(match user_specified_vis_dir.as_ref() {
            Ok(dir) => dir,
            Err(_) => "visualization/data",
        })
    } else {
        None
    };

    if let Some(path) = &vis_dir {
        if std::path::Path::new(path).exists() {
            std::fs::remove_dir_all(path)
                .expect("Failed to delete visualization directory contents");
        }
        std::fs::create_dir_all(path).expect("Failed to create visualization directory");

        // Log the absolute path after directory creation
        if let Ok(absolute_path) = std::fs::canonicalize(path) {
            tracing::info!("Visualization directory: {:?}", absolute_path);
        } else {
            tracing::info!("Visualization directory: {:?}", path);
        }
    }

    for def_id in hir_body_owners(tcx) {
        let kind = tcx.def_kind(def_id);
        if !matches!(kind, DefKind::Fn | DefKind::AssocFn) {
            continue;
        }
        let item_name = tcx.def_path_str(def_id.to_def_id()).to_string();
        if let Ok(function) = std::env::var("PCG_CHECK_FUNCTION")
            && function != item_name
        {
            tracing::debug!(
                "Skipping function: {item_name} because PCG_CHECK_FUNCTION is set to {function}"
            );
            continue;
        }
        if let Ok(function) = std::env::var("PCG_SKIP_FUNCTION")
            && function == item_name
        {
            tracing::info!(
                "Skipping function: {item_name} because PCG_SKIP_FUNCTION is set to {function}"
            );
            continue;
        }
        let body = take_stored_body(tcx, def_id);

        if !should_check_body(&body.body) {
            continue;
        }

        info!(
            "{}Running PCG on function: {} with {} basic blocks",
            cargo_crate_name().map_or("".to_string(), |name| format!("{name}: ")),
            item_name,
            body.body.basic_blocks.len()
        );
        tracing::info!("Path: {:?}", body.body.span);
        tracing::debug!("Number of basic blocks: {}", body.body.basic_blocks.len());
        tracing::debug!("Number of locals: {}", body.body.local_decls.len());
        run_pcg_on_fn(def_id, &body, tcx, polonius, vis_dir, None);
        item_names.push(item_name);
    }

    if let Some(dir_path) = &vis_dir {
        let file_path = format!("{dir_path}/functions.json");

        let json_data = serde_json::to_string(
            &item_names
                .iter()
                .map(|name| (name.clone(), name.clone()))
                .collect::<std::collections::HashMap<_, _>>(),
        )
        .expect("Failed to serialize item names to JSON");
        let mut file = File::create(file_path).expect("Failed to create JSON file");
        file.write_all(json_data.as_bytes())
            .expect("Failed to write item names to JSON file");
    }
}

type PcgCallback<'tcx> =
    dyn for<'mir, 'arena> Fn(PcgAnalysis<'mir, 'tcx, &'arena bumpalo::Bump>) + 'static;

pub(crate) fn run_pcg_on_fn<'tcx>(
    def_id: LocalDefId,
    body: &BodyWithBorrowckFacts<'tcx>,
    tcx: TyCtxt<'tcx>,
    polonius: bool,
    vis_dir: Option<&str>,
    callback: Option<&PcgCallback<'tcx>>,
) {
    let region_debug_name_overrides = if let Ok(lines) = source_lines(tcx, &body.body) {
        lines
            .iter()
            .flat_map(|l| l.split("PCG_LIFETIME_DISPLAY: ").nth(1))
            .map(|l| LifetimeRenderAnnotation::from(l).to_pair(tcx, &body.body))
            .collect::<_>()
    } else {
        BTreeMap::new()
    };
    let mut bc = if polonius {
        BorrowChecker::Polonius(PoloniusBorrowChecker::new(tcx, body))
    } else {
        BorrowChecker::Impl(BorrowCheckerImpl::new(tcx, body))
    };
    #[cfg(feature = "visualization")]
    {
        let region_printer = bc.region_pretty_printer();
        for (region, name) in region_debug_name_overrides {
            region_printer.insert(region, name.to_string());
        }
    }
    let item_name = tcx.def_path_str(def_id.to_def_id()).to_string();
    let item_dir = vis_dir.map(|dir| format!("{dir}/{item_name}"));
    let arena = Bump::new();
    let mut output = run_pcg(&body.body, tcx, &bc, &arena, item_dir.as_deref());
    let ctxt = CompilerCtxt::new(&body.body, tcx, &bc);

    #[rustversion::since(2024-12-14)]
    if let Some(dir_path) = &item_dir {
        emit_borrowcheck_graphs(dir_path, ctxt);
    }

    emit_and_check_annotations(item_name, &mut output);
    if let Some(callback) = callback {
        callback(output);
    }
}

struct LifetimeRenderAnnotation {
    var: String,
    region_idx: RegionIdx,
    display_as: String,
}

impl LifetimeRenderAnnotation {
    fn get_place<'tcx>(&self, tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Place<'tcx> {
        if self.var.starts_with('_')
            && let Ok(idx) = self.var.split_at(1).1.parse::<usize>()
        {
            let local: Local = idx.into();
            local.into()
        } else {
            CompilerCtxt::new(body, tcx, ())
                .local_place(self.var.as_str())
                .unwrap()
        }
    }

    fn to_pair<'tcx>(&self, tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> (RegionVid, String) {
        let place = self.get_place(tcx, body);
        let region: PcgRegion = place.regions(CompilerCtxt::new(body, tcx, ()))[self.region_idx];
        (region.vid().unwrap(), self.display_as.clone())
    }
}

impl From<&str> for LifetimeRenderAnnotation {
    fn from(s: &str) -> Self {
        let parts = s.split(" ").collect::<Vec<_>>();
        Self {
            var: parts[0].to_string(),
            region_idx: parts[1].parse::<usize>().unwrap().into(),
            display_as: parts[2].to_string(),
        }
    }
}

#[derive(From)]
#[allow(clippy::large_enum_variant)]
enum BorrowChecker<'mir, 'tcx> {
    Polonius(PoloniusBorrowChecker<'mir, 'tcx>),
    Impl(BorrowCheckerImpl<'mir, 'tcx>),
}

#[cfg(feature = "visualization")]
impl<'mir, 'tcx> BorrowChecker<'mir, 'tcx> {
    fn region_pretty_printer(&mut self) -> &mut RegionPrettyPrinter<'mir, 'tcx> {
        match self {
            BorrowChecker::Polonius(bc) => &mut bc.pretty_printer,
            BorrowChecker::Impl(bc) => &mut bc.pretty_printer,
        }
    }
}

impl<'tcx> BorrowCheckerInterface<'tcx> for BorrowChecker<'_, 'tcx> {
    fn is_live(&self, node: pcg::PCGNode<'tcx>, location: Location) -> bool {
        match self {
            BorrowChecker::Polonius(bc) => bc.is_live(node, location),
            BorrowChecker::Impl(bc) => bc.is_live(node, location),
        }
    }

    fn outlives(&self, sup: PcgRegion, sub: PcgRegion) -> bool {
        match self {
            BorrowChecker::Polonius(bc) => bc.outlives(sup, sub),
            BorrowChecker::Impl(bc) => bc.outlives(sup, sub),
        }
    }

    fn twophase_borrow_activations(
        &self,
        location: Location,
    ) -> std::collections::BTreeSet<Location> {
        match self {
            BorrowChecker::Polonius(bc) => bc.twophase_borrow_activations(location),
            BorrowChecker::Impl(bc) => bc.twophase_borrow_activations(location),
        }
    }

    fn region_infer_ctxt(&self) -> &borrowck::RegionInferenceContext<'tcx> {
        match self {
            BorrowChecker::Polonius(bc) => bc.region_infer_ctxt(),
            BorrowChecker::Impl(bc) => bc.region_infer_ctxt(),
        }
    }

    fn location_table(&self) -> &LocationTable {
        match self {
            BorrowChecker::Polonius(bc) => bc.location_table(),
            BorrowChecker::Impl(bc) => bc.location_table(),
        }
    }

    fn polonius_output(&self) -> Option<&borrowck::PoloniusOutput> {
        match self {
            BorrowChecker::Polonius(bc) => bc.polonius_output(),
            BorrowChecker::Impl(bc) => bc.polonius_output(),
        }
    }

    fn as_dyn(&self) -> &dyn BorrowCheckerInterface<'tcx> {
        self
    }

    fn borrow_set(&self) -> &borrowck::BorrowSet<'tcx> {
        match self {
            BorrowChecker::Polonius(bc) => bc.borrow_set(),
            BorrowChecker::Impl(bc) => bc.borrow_set(),
        }
    }

    fn input_facts(&self) -> &borrowck::PoloniusInput {
        match self {
            BorrowChecker::Polonius(bc) => bc.input_facts(),
            BorrowChecker::Impl(bc) => bc.input_facts(),
        }
    }

    fn override_region_debug_string(&self, _region: RegionVid) -> Option<&str> {
        match self {
            BorrowChecker::Polonius(bc) => bc.override_region_debug_string(_region),
            BorrowChecker::Impl(bc) => bc.override_region_debug_string(_region),
        }
    }

    fn blocks(
        &self,
        candidate_blocker: LocalRegionProjection<'tcx>,
        borrowed_place: Place<'tcx>,
        location: Location,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        match self {
            BorrowChecker::Polonius(bc) => {
                bc.blocks(candidate_blocker, borrowed_place, location, ctxt)
            }
            BorrowChecker::Impl(bc) => bc.blocks(candidate_blocker, borrowed_place, location, ctxt),
        }
    }

    fn borrows_out_of_scope_at(&self, location: Location) -> BTreeSet<BorrowIndex> {
        match self {
            BorrowChecker::Polonius(bc) => bc.borrows_out_of_scope_at(location),
            BorrowChecker::Impl(bc) => bc.borrows_out_of_scope_at(location),
        }
    }
}

fn emit_and_check_annotations(item_name: String, output: &mut PcgOutput<'_, '_, &bumpalo::Bump>) {
    let emit_pcg_annotations = env_feature_enabled("PCG_EMIT_ANNOTATIONS").unwrap_or(false);
    let check_pcg_annotations = env_feature_enabled("PCG_CHECK_ANNOTATIONS").unwrap_or(false);

    let ctxt = output.ctxt();

    if emit_pcg_annotations || check_pcg_annotations {
        let mut debug_lines = Vec::new();

        if let Some(err) = output.first_error() {
            debug_lines.push(format!("{err:?}"));
        }
        for block in ctxt.body().basic_blocks.indices() {
            if let Ok(Some(state)) = output.get_all_for_bb(block) {
                for line in state.debug_lines(ctxt) {
                    debug_lines.push(line);
                }
            }
        }
        if emit_pcg_annotations {
            for line in debug_lines.iter() {
                eprintln!("// PCG: {line}");
            }
        }
        if check_pcg_annotations {
            if let Ok(source) = source_lines(ctxt.tcx(), ctxt.body()) {
                let debug_lines_set: FxHashSet<_> = debug_lines.into_iter().collect();
                let expected_annotations = source
                    .iter()
                    .flat_map(|l| l.split("// PCG: ").nth(1))
                    .map(|l| l.trim())
                    .collect::<Vec<_>>();
                let not_expected_annotations = source
                    .iter()
                    .flat_map(|l| l.split("// ~PCG: ").nth(1))
                    .map(|l| l.trim())
                    .collect::<Vec<_>>();
                let missing_annotations = expected_annotations
                    .iter()
                    .filter(|a| !debug_lines_set.contains(**a))
                    .collect::<Vec<_>>();
                if !missing_annotations.is_empty() {
                    panic!("Missing annotations: {missing_annotations:?}");
                }
                for not_expected_annotation in not_expected_annotations {
                    if debug_lines_set.contains(not_expected_annotation) {
                        panic!("Unexpected annotation: {not_expected_annotation}");
                    }
                }
            } else {
                tracing::warn!("No source for function: {}", item_name);
            }
        }
    }
}

fn source_lines(tcx: TyCtxt<'_>, mir: &Body<'_>) -> Result<Vec<String>, SpanSnippetError> {
    let source_map = tcx.sess.source_map();
    let span = mir.span;
    let lines = source_map.span_to_snippet(span)?;
    Ok(lines.lines().map(|l| l.to_string()).collect())
}

#[rustversion::since(2024-12-14)]
fn emit_borrowcheck_graphs<'a, 'tcx: 'a, 'bc>(
    dir_path: &str,
    ctxt: CompilerCtxt<'a, 'tcx, &'bc BorrowChecker<'a, 'tcx>>,
) {
    if let BorrowChecker::Polonius(bc) = ctxt.bc() {
        let ctxt = CompilerCtxt::new(ctxt.body(), ctxt.tcx(), bc);
        for (block_index, data) in ctxt.body().basic_blocks.iter_enumerated() {
            let num_stmts = data.statements.len();
            for stmt_index in 0..num_stmts + 1 {
                let location = Location {
                    block: block_index,
                    statement_index: stmt_index,
                };
                let start_dot_graph = subset_at_location(location, true, ctxt);
                let start_file_path =
                    format!("{dir_path}/bc_facts_graph_{block_index:?}_{stmt_index}_start.dot");
                start_dot_graph
                    .write_to_file(start_file_path.as_str())
                    .unwrap();
                let mid_dot_graph = subset_at_location(location, false, ctxt);
                let mid_file_path =
                    format!("{dir_path}/bc_facts_graph_{block_index:?}_{stmt_index}_mid.dot");
                mid_dot_graph.write_to_file(mid_file_path.as_str()).unwrap();

                let mut bc_facts_file = std::fs::File::create(format!(
                    "{dir_path}/bc_facts_{block_index:?}_{stmt_index}.txt"
                ))
                .unwrap();

                fn write_loans(
                    loans: BTreeMap<RegionVid, BTreeSet<BorrowIndex>>,
                    loans_file: &mut std::fs::File,
                    ctxt: CompilerCtxt<'_, '_, &PoloniusBorrowChecker<'_, '_>>,
                ) {
                    for (region, indices) in loans {
                        writeln!(loans_file, "Region: {region:?}").unwrap();
                        for index in indices {
                            writeln!(loans_file, "  {:?}", ctxt.bc().borrow_set()[index].region())
                                .unwrap();
                        }
                    }
                }

                fn write_bc_facts(
                    location: RichLocation,
                    bc_facts_file: &mut std::fs::File,
                    ctxt: CompilerCtxt<'_, '_, &PoloniusBorrowChecker<'_, '_>>,
                ) {
                    let origin_contains_loan_at = ctxt.bc().origin_contains_loan_at_map(location);
                    writeln!(bc_facts_file, "{location:?} Origin contains loan at:").unwrap();
                    if let Some(origin_contains_loan_at) = origin_contains_loan_at {
                        write_loans(origin_contains_loan_at, bc_facts_file, ctxt);
                    }
                    writeln!(bc_facts_file, "{location:?} Origin live on entry:").unwrap();
                    if let Some(origin_live_on_entry) = ctxt.bc().origin_live_on_entry(location) {
                        for region in origin_live_on_entry {
                            writeln!(bc_facts_file, "  Region: {region:?}").unwrap();
                        }
                    }
                    writeln!(bc_facts_file, "{location:?} Loans live at:").unwrap();
                    for region in ctxt.bc().loans_live_at(location) {
                        writeln!(bc_facts_file, "  Region: {region:?}").unwrap();
                    }
                }

                let start_location = RichLocation::Start(location);
                let mid_location = RichLocation::Mid(location);
                write_bc_facts(start_location, &mut bc_facts_file, ctxt);
                write_bc_facts(mid_location, &mut bc_facts_file, ctxt);
            }
        }
        let dot_graph = subset_anywhere(ctxt);
        let file_path = format!("{dir_path}/bc_facts_graph_anywhere.dot");
        dot_graph.write_to_file(file_path.as_str()).unwrap();
    }

    let region_inference_dot_graph = region_inference_outlives(ctxt);
    let file_path = format!("{dir_path}/region_inference_outlives.dot");
    std::fs::write(file_path, region_inference_dot_graph).unwrap();
}
