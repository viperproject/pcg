#![feature(rustc_private)]

use std::fs::File;
use std::io::Write;

use pcs::utils::PlaceRepacker;
use std::cell::RefCell;
use tracing::{debug, info, trace, warn};
use tracing_subscriber;

use pcs::rustc_interface::{
    borrowck::consumers,
    data_structures::fx::FxHashMap,
    driver::{self, Compilation},
    hir::{self, def_id::LocalDefId},
    interface::{interface::Compiler, Config, Queries},
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
    let consumer_opts = consumers::ConsumerOptions::PoloniusInputFacts;
    debug!(
        "Start mir_borrowck for {}",
        tcx.def_path_str(def_id.to_def_id())
    );
    let body_with_facts = consumers::get_body_with_borrowck_facts(tcx, def_id, consumer_opts);
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
    pcs::rustc_interface::borrowck::provide(&mut providers);
    let original_mir_borrowck = providers.mir_borrowck;
    original_mir_borrowck(tcx, def_id)
}

#[allow(unused)]
fn should_check_body(body: &BodyWithBorrowckFacts<'_>) -> bool {
    // DEBUG
    body.body.basic_blocks.len() < 32

    // true
}

fn run_pcg_on_all_fns<'tcx>(tcx: TyCtxt<'tcx>) {
    let mut item_names = vec![];

    let vis_dir = if env_feature_enabled("PCG_VISUALIZATION").unwrap_or(false) {
        Some("visualization/data")
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
                let item_name = format!("{}", tcx.def_path_str(def_id.to_def_id()));
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
                if should_check_body(&body) {
                    let mut output = run_combined_pcs(
                        &body,
                        tcx,
                        vis_dir.map(|dir| format!("{}/{}", dir, item_name)),
                    );
                    if emit_pcg_annotations || check_pcg_annotations {
                        let mut debug_lines = Vec::new();
                        for (idx, _) in body.body.basic_blocks.iter_enumerated() {
                            let block = output.get_all_for_bb(idx);
                            debug_lines
                                .extend(block.debug_lines(PlaceRepacker::new(&body.body, tcx)));
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
                                let expected_annotations = source
                                    .lines()
                                    .flat_map(|l| l.split("// PCG: ").nth(1))
                                    .map(|l| l.trim())
                                    .collect::<Vec<_>>();
                                if !expected_annotations.is_empty() {
                                    let missing_annotations = expected_annotations
                                        .iter()
                                        .filter(|a| !debug_lines.contains(&a.to_string()))
                                        .collect::<Vec<_>>();
                                    if !missing_annotations.is_empty() {
                                        panic!("Missing annotations: {:?}", missing_annotations);
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
    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        queries.global_ctxt().unwrap().enter(run_pcg_on_all_fns);
        if std::env::var("CARGO").is_ok() {
            Compilation::Continue
        } else {
            Compilation::Stop
        }
    }
}

fn main() {
    // Initialize tracing
    tracing_subscriber::fmt()
        .with_max_level(tracing::Level::INFO)
        .with_writer(std::io::stderr)
        .init();

    // This first argument will be removed!
    // See `driver::RunCompiler::run` for more details
    let mut rustc_args = vec!["rustc".to_string()];

    if !std::env::args().any(|arg| arg.starts_with("--edition=")) {
        rustc_args.push("--edition=2018".to_string());
    }
    // rustc_args.push("-Zpolonius=next".to_string());
    rustc_args.extend(std::env::args().skip(1));

    let args_str = rustc_args
        .iter()
        .map(|arg| shell_escape::escape(arg.into()))
        .collect::<Vec<_>>()
        .join(" ");
    trace!("Running rustc with args: {}", args_str);

    let mut callbacks = PcsCallbacks;
    driver::RunCompiler::new(&rustc_args, &mut callbacks)
        .run()
        .unwrap();
}
