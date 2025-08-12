use std::path::Path;
use std::sync::Arc;
use std::{fs, io};

use crate::owned_pcg::PcgAnalysis;
#[rustversion::since(2025-05-24)]
use crate::rustc_interface::driver::run_compiler;
use crate::rustc_interface::driver::{self, Compilation};
use crate::rustc_interface::hir::def::DefKind;
use crate::rustc_interface::interface::{Config, interface::Compiler};
use crate::rustc_interface::middle::ty::TyCtxt;
use crate::rustc_interface::span::source_map::FileLoader;
use crate::utils::callbacks::set_mir_borrowck;

use super::callbacks::{in_cargo_crate, run_pcg_on_fn, take_stored_body};

#[allow(unused)]
pub struct TestCallbacks {
    input: String,
    callback: Option<
        Box<
            dyn for<'mir, 'tcx, 'arena> Fn(PcgAnalysis<'mir, 'tcx, &'arena bumpalo::Bump>)
                + Send
                + Sync
                + 'static,
        >,
    >,
}

pub struct StringLoader(pub String);
impl FileLoader for StringLoader {
    fn file_exists(&self, _: &Path) -> bool {
        true
    }

    fn read_file(&self, _: &Path) -> io::Result<String> {
        Ok(self.0.clone())
    }

    fn read_binary_file(&self, path: &Path) -> io::Result<Arc<[u8]>> {
        Ok(fs::read(path)?.into())
    }
}

/// # Safety
///
/// Stored bodies must come from the same `tcx`.
#[rustversion::since(2025-05-24)]
unsafe fn run_pcg_on_first_fn<'tcx>(
    tcx: TyCtxt<'tcx>,
    callback: impl for<'mir, 'arena> Fn(PcgAnalysis<'mir, 'tcx, &'arena bumpalo::Bump>)
    + Send
    + Sync
    + 'static,
) {
    let def_id = tcx
        .hir_body_owners()
        .find(|def_id| matches!(tcx.def_kind(*def_id), DefKind::Fn | DefKind::AssocFn))
        .unwrap();
    // SAFETY: bodies come from the same `tcx`
    let body = unsafe { take_stored_body(tcx, def_id) };
    run_pcg_on_fn(def_id, &body, tcx, false, None, Some(&callback));
}

#[rustversion::since(2025-05-24)]
impl driver::Callbacks for TestCallbacks {
    fn config(&mut self, config: &mut Config) {
        assert!(config.override_queries.is_none());
        config.override_queries = Some(set_mir_borrowck);
        config.file_loader = Some(Box::new(StringLoader(self.input.clone())));
    }

    fn after_analysis(&mut self, _compiler: &Compiler, tcx: TyCtxt<'_>) -> Compilation {
        tracing::info!("after_analysis");
        // SAFETY: `config()` overrides the borrowck query to save the bodies
        // from this  `tcx`.
        unsafe {
            run_pcg_on_first_fn(tcx, self.callback.take().unwrap());
        }
        if in_cargo_crate() {
            Compilation::Continue
        } else {
            Compilation::Stop
        }
    }
}

#[cfg(test)]
#[rustversion::since(2025-05-24)]
pub(crate) fn run_pcg_on_str(
    input: &str,
    callback: impl for<'mir, 'tcx, 'arena> Fn(PcgAnalysis<'mir, 'tcx, &'arena bumpalo::Bump>)
    + Send
    + Sync
    + 'static,
) {
    run_compiler(
        &vec![
            "rustc".to_string(),
            "dummy.rs".to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
            "--edition=2021".to_string(),
        ],
        &mut TestCallbacks {
            input: input.to_string(),
            callback: Some(Box::new(callback)),
        },
    );
}
