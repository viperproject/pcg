#![feature(rustc_private)]
#![feature(let_chains)]
#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]

#[cfg(feature = "memory_profiling")]
#[cfg(not(target_env = "msvc"))]
#[cfg(not(target_os = "macos"))]
#[global_allocator]
static GLOBAL: tikv_jemallocator::Jemalloc = tikv_jemallocator::Jemalloc;

#[cfg(feature = "memory_profiling")]
#[cfg(not(target_os = "macos"))]
#[allow(non_upper_case_globals)]
#[export_name = "malloc_conf"]
pub static malloc_conf: &[u8] = b"prof:true,prof_active:true,lg_prof_sample:19\0";

use std::fs::File;
use std::io::Write;

use derive_more::From;
use pcg::borrow_pcg::borrow_checker::r#impl::{BorrowCheckerImpl, PoloniusBorrowChecker};
use pcg::borrow_pcg::coupling_graph_constructor::BorrowCheckerInterface;
use pcg::utils::CompilerCtxt;

#[rustversion::since(2024-12-14)]
use pcg::visualization::bc_facts_graph::{
    region_inference_outlives, subset_anywhere, subset_at_location,
};

use pcg::{run_pcg, PcgOutput};
use std::cell::RefCell;
use tracing::{debug, info, trace};

use pcg::rustc_interface::middle::mir::Location;

#[rustversion::before(2024-11-09)]
use pcg::rustc_interface::interface::Queries;

use pcg::rustc_interface::{
    borrowck,
    data_structures::fx::{FxHashMap, FxHashSet},
    driver::{self, Compilation},
    hir::{self, def_id::LocalDefId},
    interface::{interface::Compiler, Config},
    middle::{
        query::queries::mir_borrowck::ProvidedValue as MirBorrowck, ty::TyCtxt, util::Providers,
    },
    session::Session,
};
use pcg::{pcg::BodyWithBorrowckFacts, utils::env_feature_enabled};

struct PcsCallbacks;

thread_local! {
    pub static BODIES:
        RefCell<FxHashMap<LocalDefId, BodyWithBorrowckFacts<'static>>> =
        RefCell::new(FxHashMap::default());
}

fn mir_borrowck<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> MirBorrowck<'tcx> {
    let consumer_opts = borrowck::ConsumerOptions::PoloniusInputFacts;
    debug!(
        "Start mir_borrowck for {}",
        tcx.def_path_str(def_id.to_def_id())
    );
    let body_with_facts = borrowck::get_body_with_borrowck_facts(tcx, def_id, consumer_opts);
    debug!(
        "End mir_borrowck for {}",
        tcx.def_path_str(def_id.to_def_id())
    );
    unsafe {
        let body: BodyWithBorrowckFacts<'tcx> = body_with_facts.into();
        let body: BodyWithBorrowckFacts<'static> = std::mem::transmute(body);
        BODIES.with(|state| {
            let mut map = state.borrow_mut();
            trace!(
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

#[allow(unused)]
fn should_check_body(body: &BodyWithBorrowckFacts<'_>) -> bool {
    true
}

fn cargo_crate_name() -> Option<String> {
    std::env::var("CARGO_CRATE_NAME").ok()
}

fn in_cargo_crate() -> bool {
    cargo_crate_name().is_some()
}

#[rustversion::since(2024-12-14)]
fn emit_borrowcheck_graphs(dir_path: &str, polonius: bool, ctxt: CompilerCtxt<'_, '_, '_>) {
    if polonius {
        for (block_index, data) in ctxt.body().basic_blocks.iter_enumerated() {
            let num_stmts = data.statements.len();
            for stmt_index in 0..num_stmts + 1 {
                let location = Location {
                    block: block_index,
                    statement_index: stmt_index,
                };
                let start_dot_graph = subset_at_location(location, true, ctxt);
                let start_file_path = format!(
                    "{}/bc_facts_graph_{:?}_{}_start.dot",
                    dir_path, block_index, stmt_index
                );
                start_dot_graph
                    .write_to_file(start_file_path.as_str())
                    .unwrap();
                let mid_dot_graph = subset_at_location(location, false, ctxt);
                let mid_file_path = format!(
                    "{}/bc_facts_graph_{:?}_{}_mid.dot",
                    dir_path, block_index, stmt_index
                );
                mid_dot_graph.write_to_file(mid_file_path.as_str()).unwrap();
            }
        }
        let dot_graph = subset_anywhere(ctxt);
        let file_path = format!("{}/bc_facts_graph_anywhere.dot", dir_path);
        dot_graph.write_to_file(file_path.as_str()).unwrap();
    }

    let region_inference_dot_graph = region_inference_outlives(ctxt);
    let file_path = format!("{}/region_inference_outlives.dot", dir_path);
    std::fs::write(file_path, region_inference_dot_graph).unwrap();
}

fn emit_and_check_annotations(item_name: String, output: &mut PcgOutput<'_, '_, '_>) {
    let emit_pcg_annotations = env_feature_enabled("PCG_EMIT_ANNOTATIONS").unwrap_or(false);
    let check_pcg_annotations = env_feature_enabled("PCG_CHECK_ANNOTATIONS").unwrap_or(false);

    let ctxt = output.ctxt();

    if emit_pcg_annotations || check_pcg_annotations {
        let mut debug_lines = Vec::new();

        if let Some(err) = output.first_error() {
            debug_lines.push(format!("{:?}", err));
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
                eprintln!("// PCG: {}", line);
            }
        }
        if check_pcg_annotations {
            if let Ok(source) = ctxt
                .tcx()
                .sess
                .source_map()
                .span_to_snippet(ctxt.body().span)
            {
                let debug_lines_set: FxHashSet<_> = debug_lines.into_iter().collect();
                let expected_annotations = source
                    .lines()
                    .flat_map(|l| l.split("// PCG: ").nth(1))
                    .map(|l| l.trim())
                    .collect::<Vec<_>>();
                let not_expected_annotations = source
                    .lines()
                    .flat_map(|l| l.split("// ~PCG: ").nth(1))
                    .map(|l| l.trim())
                    .collect::<Vec<_>>();
                let missing_annotations = expected_annotations
                    .iter()
                    .filter(|a| !debug_lines_set.contains(**a))
                    .collect::<Vec<_>>();
                if !missing_annotations.is_empty() {
                    panic!("Missing annotations: {:?}", missing_annotations);
                }
                for not_expected_annotation in not_expected_annotations {
                    if debug_lines_set.contains(not_expected_annotation) {
                        panic!("Unexpected annotation: {}", not_expected_annotation);
                    }
                }
            } else {
                tracing::warn!("No source for function: {}", item_name);
            }
        }
    }
}

#[derive(From)]
enum BorrowChecker<'mir, 'tcx> {
    Polonius(PoloniusBorrowChecker<'mir, 'tcx>),
    Impl(BorrowCheckerImpl<'mir, 'tcx>),
}
impl<'mir, 'tcx> BorrowCheckerInterface<'mir, 'tcx> for BorrowChecker<'mir, 'tcx> {
    fn is_live(&self, node: pcg::pcg::PCGNode<'tcx>, location: Location) -> bool {
        match self {
            BorrowChecker::Polonius(bc) => bc.is_live(node, location),
            BorrowChecker::Impl(bc) => bc.is_live(node, location),
        }
    }

    fn outlives(
        &self,
        sup: pcg::borrow_pcg::region_projection::PcgRegion,
        sub: pcg::borrow_pcg::region_projection::PcgRegion,
    ) -> bool {
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

    fn region_inference_ctxt(&self) -> &borrowck::RegionInferenceContext<'tcx> {
        match self {
            BorrowChecker::Polonius(bc) => bc.region_inference_ctxt(),
            BorrowChecker::Impl(bc) => bc.region_inference_ctxt(),
        }
    }

    fn location_table(&self) -> &borrowck::LocationTable {
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

    fn as_dyn(&self) -> &dyn BorrowCheckerInterface<'mir, 'tcx> {
        self
    }
}

fn run_pcg_on_fn<'tcx>(
    def_id: LocalDefId,
    body: &BodyWithBorrowckFacts<'tcx>,
    tcx: TyCtxt<'tcx>,
    polonius: bool,
    vis_dir: Option<&str>,
) {
    let bc = if polonius {
        BorrowChecker::Polonius(PoloniusBorrowChecker::new(tcx, body))
    } else {
        BorrowChecker::Impl(BorrowCheckerImpl::new(tcx, body))
    };
    let item_name = tcx.def_path_str(def_id.to_def_id()).to_string();
    let item_dir = vis_dir.map(|dir| format!("{}/{}", dir, item_name));
    let mut output = run_pcg(&body.body, tcx, &bc, item_dir.as_deref());
    let ctxt = output.ctxt();

    #[rustversion::since(2024-12-14)]
    if let Some(dir_path) = &item_dir {
        emit_borrowcheck_graphs(dir_path, polonius, ctxt);
    }

    emit_and_check_annotations(item_name, &mut output);
}

fn run_pcg_on_all_fns<'tcx>(tcx: TyCtxt<'tcx>, polonius: bool) {
    if in_cargo_crate() && std::env::var("CARGO_PRIMARY_PACKAGE").is_err() {
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
    }

    for def_id in tcx.hir().body_owners() {
        let kind = tcx.def_kind(def_id);
        if !matches!(kind, hir::def::DefKind::Fn | hir::def::DefKind::AssocFn) {
            continue;
        }
        let item_name = tcx.def_path_str(def_id.to_def_id()).to_string();
        let body: BodyWithBorrowckFacts<'tcx> = BODIES.with(|state| {
            let mut map = state.borrow_mut();
            unsafe {
                std::mem::transmute(
                    map.remove(&def_id)
                        .unwrap_or_else(|| panic!("No body found for {}", item_name)),
                )
            }
        });

        info!(
            "{}Running PCG on function: {}",
            cargo_crate_name().map_or("".to_string(), |name| format!("{}: ", name)),
            item_name
        );
        tracing::debug!("Path: {:?}", body.body.span);
        tracing::debug!("Number of basic blocks: {}", body.body.basic_blocks.len());
        tracing::debug!("Number of locals: {}", body.body.local_decls.len());
        if should_check_body(&body) {
            run_pcg_on_fn(def_id, &body, tcx, polonius, vis_dir);
        }
        item_names.push(item_name);
    }

    if let Some(dir_path) = &vis_dir {
        let file_path = format!("{}/functions.json", dir_path);

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

fn set_mir_borrowck(_session: &Session, providers: &mut Providers) {
    providers.mir_borrowck = mir_borrowck;
}

impl driver::Callbacks for PcsCallbacks {
    fn config(&mut self, config: &mut Config) {
        assert!(config.override_queries.is_none());
        config.override_queries = Some(set_mir_borrowck);
    }

    #[rustversion::before(2024-11-09)]
    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        queries.global_ctxt().unwrap().enter(|tcx| {
            run_pcg_on_all_fns(tcx, env_feature_enabled("PCG_POLONIUS").unwrap_or(false))
        });
        if in_cargo_crate() {
            Compilation::Continue
        } else {
            Compilation::Stop
        }
    }

    #[rustversion::since(2024-11-09)]
    fn after_analysis(&mut self, _compiler: &Compiler, tcx: TyCtxt<'_>) -> Compilation {
        run_pcg_on_all_fns(tcx, env_feature_enabled("PCG_POLONIUS").unwrap_or(false));
        if in_cargo_crate() {
            Compilation::Continue
        } else {
            Compilation::Stop
        }
    }
}

#[rustversion::before(2024-12-14)]
fn go(args: Vec<String>) {
    driver::RunCompiler::new(&args, &mut PcsCallbacks)
        .run()
        .unwrap()
}

#[rustversion::since(2024-12-14)]
fn go(args: Vec<String>) {
    driver::RunCompiler::new(&args, &mut PcsCallbacks).run()
}

#[cfg(feature = "memory_profiling")]
async fn handle_get_heap(
) -> Result<impl axum::response::IntoResponse, (axum::http::StatusCode, String)> {
    let mut prof_ctl = jemalloc_pprof::PROF_CTL.as_ref().unwrap().lock().await;
    if !prof_ctl.activated() {
        return Err((
            axum::http::StatusCode::FORBIDDEN,
            "heap profiling not activated".into(),
        ));
    }
    let pprof = prof_ctl.dump_pprof().map_err(|err| {
        (
            axum::http::StatusCode::INTERNAL_SERVER_ERROR,
            err.to_string(),
        )
    })?;
    Ok(pprof)
}

#[cfg(feature = "memory_profiling")]
async fn start_profiling_server() {
    let app = axum::Router::new().route("/debug/pprof/heap", axum::routing::get(handle_get_heap));

    let listener = tokio::net::TcpListener::bind("0.0.0.0:4444").await.unwrap();
    info!("Started profiling server on port 4444");
    tokio::spawn(async move {
        axum::serve(listener, app).await.unwrap();
    });
}

fn setup_rustc_args() -> Vec<String> {
    // This first argument is ultimately removed, actually
    let mut rustc_args = vec!["rustc".to_string()];

    if !std::env::args().any(|arg| arg.starts_with("--edition=")) {
        rustc_args.push("--edition=2018".to_string());
    }
    if env_feature_enabled("PCG_POLONIUS").unwrap_or(false) {
        rustc_args.push("-Zpolonius".to_string());
    }
    if !in_cargo_crate() {
        rustc_args.push("-Zno-codegen".to_string());
    }
    rustc_args.extend(std::env::args().skip(1));

    let args_str = rustc_args
        .iter()
        .map(|arg| shell_escape::escape(arg.into()))
        .collect::<Vec<_>>()
        .join(" ");
    trace!("Running rustc with args: {}", args_str);

    rustc_args
}

fn init_tracing() {
    tracing_subscriber::fmt()
        .with_max_level(tracing::Level::INFO)
        .with_writer(std::io::stderr)
        .init();
}

#[cfg(feature = "memory_profiling")]
#[tokio::main]
async fn main() {
    init_tracing();
    start_profiling_server().await;
    go(setup_rustc_args());
}

#[cfg(not(feature = "memory_profiling"))]
fn main() {
    init_tracing();
    go(setup_rustc_args());
}
