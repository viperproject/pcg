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

use pcg::utils::{callbacks::{in_cargo_crate, PcgCallbacks}, DUMP_MIR_DATAFLOW, POLONIUS};

#[rustversion::since(2025-03-02)]
use pcg::rustc_interface::driver::run_compiler;

use tracing::trace;

#[rustversion::before(2024-11-09)]
use pcg::rustc_interface::interface::Queries;

#[rustversion::before(2024-12-14)]
fn go(args: Vec<String>) {
    driver::RunCompiler::new(&args, &mut PcgCallbacks)
        .run()
        .unwrap()
}

#[rustversion::nightly(2024-12-14)]
fn go(args: Vec<String>) {
    driver::RunCompiler::new(&args, &mut PcgCallbacks).run()
}

#[rustversion::since(2025-03-02)]
fn go(args: Vec<String>) {
    run_compiler(&args, &mut PcgCallbacks)
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
    tracing::info!("Started profiling server on port 4444");
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
    if *POLONIUS {
        rustc_args.push("-Zpolonius".to_string());
    }
    if *DUMP_MIR_DATAFLOW {
        rustc_args.push("-Zdump-mir=all".to_string());
        rustc_args.push("-Zdump-mir-dataflow".to_string());
    }
    if !in_cargo_crate() {
        rustc_args.push("-Zno-codegen".to_string());
    }

    // http crate for top crates eval.
    rustc_args.push("-Adangerous_implicit_autorefs".to_string());

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
