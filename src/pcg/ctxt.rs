use crate::rustc_interface::middle::{mir, ty};
use crate::utils::logging::LogPredicate;
use crate::utils::{CompilerCtxt, HasCompilerCtxt, PcgSettings, SETTINGS};

#[derive(Copy, Clone)]
pub(crate) struct AnalysisCtxt<'a, 'tcx> {
    pub(crate) ctxt: CompilerCtxt<'a, 'tcx>,
    pub(crate) settings: &'a PcgSettings<'a>,
    pub(crate) block: mir::BasicBlock,
}

impl<'a, 'tcx> HasCompilerCtxt<'a, 'tcx> for AnalysisCtxt<'a, 'tcx> {
    fn ctxt(&self) -> CompilerCtxt<'a, 'tcx> {
        self.ctxt
    }
}

impl<'a, 'tcx> AnalysisCtxt<'a, 'tcx> {
    pub(crate) fn tcx(&self) -> ty::TyCtxt<'tcx> {
        self.ctxt.tcx()
    }
    pub(crate) fn body(&self) -> &'a mir::Body<'tcx> {
        self.ctxt.body()
    }
    pub(crate) fn new(ctxt: CompilerCtxt<'a, 'tcx>, block: mir::BasicBlock) -> Self {
        Self {
            ctxt,
            settings: &SETTINGS,
            block,
        }
    }
    pub(crate) fn matches(&self, predicate: LogPredicate) -> bool {
        match predicate {
            LogPredicate::DebugBlock => {
                if let Some(debug_block) = self.settings.debug_block {
                    debug_block == self.block
                } else {
                    false
                }
            }
        }
    }
}
