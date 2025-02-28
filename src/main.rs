#![feature(rustc_private)]

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

use pcs::utils::PlaceRepacker;
use std::cell::RefCell;
use tracing::{debug, info, trace, warn};

#[rustversion::before(2024-11-09)]
use pcs::rustc_interface::interface::Queries;

use pcs::rustc_interface::{
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
use pcs::{combined_pcs::BodyWithBorrowckFacts, run_combined_pcs, utils::env_feature_enabled};

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

fn in_cargo_crate() -> bool {
    std::env::var("CARGO_CRATE_NAME").is_ok()
}

fn run_pcg_on_all_fns(tcx: TyCtxt<'_>) {
    if in_cargo_crate() && std::env::var("CARGO_PRIMARY_PACKAGE").is_err() {
        // We're running in cargo, but not compiling the primary package
        // We don't want to check dependencies, so abort
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

    let emit_pcg_annotations = env_feature_enabled("PCG_EMIT_ANNOTATIONS").unwrap_or(false);
    let check_pcg_annotations = env_feature_enabled("PCG_CHECK_ANNOTATIONS").unwrap_or(false);

    if let Some(path) = &vis_dir {
        if std::path::Path::new(path).exists() {
            std::fs::remove_dir_all(path)
                .expect("Failed to delete visualization directory contents");
        }
        std::fs::create_dir_all(path).expect("Failed to create visualization directory");
    }

    for def_id in tcx.hir().body_owners() {
        let kind = tcx.def_kind(def_id);
        match kind {
            hir::def::DefKind::Fn | hir::def::DefKind::AssocFn => {
                let item_name = tcx.def_path_str(def_id.to_def_id()).to_string();
                let body: BodyWithBorrowckFacts<'_> = BODIES.with(|state| {
                    let mut map = state.borrow_mut();
                    unsafe {
                        std::mem::transmute(
                            map.remove(&def_id)
                                .unwrap_or_else(|| panic!("No body found for {}", item_name)),
                        )
                    }
                });

                let safety = tcx.fn_sig(def_id).skip_binder().safety();
                if safety == hir::Safety::Unsafe {
                    warn!("Skipping unsafe function: {}", item_name);
                    continue;
                }
                info!("Running PCG on function: {}", item_name);
                info!("Path: {:?}", body.body.span);
                info!("Number of basic blocks: {}", body.body.basic_blocks.len());
                info!("Number of locals: {}", body.body.local_decls.len());
                if should_check_body(&body) {
                    let mut output = run_combined_pcs(
                        &body,
                        tcx,
                        vis_dir.map(|dir| format!("{}/{}", dir, item_name)),
                    );
                    if emit_pcg_annotations || check_pcg_annotations {
                        let mut debug_lines = Vec::new();
                        for (idx, _) in body.body.basic_blocks.iter_enumerated() {
                            if let Ok(Some(block)) = output.get_all_for_bb(idx) {
                                debug_lines
                                    .extend(block.debug_lines(PlaceRepacker::new(&body.body, tcx)));
                            }
                        }
                        if emit_pcg_annotations {
                            for line in debug_lines.iter() {
                                eprintln!("// PCG: {}", line);
                            }
                        }
                        if check_pcg_annotations {
                            if let Ok(source) =
                                tcx.sess.source_map().span_to_snippet(body.body.span)
                            {
                                let debug_lines_set: FxHashSet<_> =
                                    debug_lines.into_iter().collect();
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
                                        panic!(
                                            "Unexpected annotation: {}",
                                            not_expected_annotation
                                        );
                                    }
                                }
                            } else {
                                tracing::warn!("No source for function: {}", item_name);
                            }
                        }
                    }
                }
                item_names.push(item_name);
            }
            unsupported_item_kind => {
                eprintln!("Unsupported item: {unsupported_item_kind:?}");
            }
        }
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
        info!("config");
        assert!(config.override_queries.is_none());
        config.override_queries = Some(set_mir_borrowck);
    }

    #[rustversion::before(2024-11-09)]
    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        queries.global_ctxt().unwrap().enter(run_pcg_on_all_fns);
        if in_cargo_crate() {
            Compilation::Continue
        } else {
            Compilation::Stop
        }
    }

    #[rustversion::since(2024-11-09)]
    fn after_analysis(&mut self, _compiler: &Compiler, tcx: TyCtxt<'_>) -> Compilation {
        run_pcg_on_all_fns(tcx);
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
