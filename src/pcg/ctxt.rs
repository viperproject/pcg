use crate::rustc_interface::middle::mir;
use crate::utils::logging::LogPredicate;
use crate::utils::{CompilerCtxt, PcgSettings, SETTINGS};

pub(crate) trait AnalysisCtxt<'a, 'tcx>: Copy {
    fn ctxt(self) -> CompilerCtxt<'a, 'tcx>;
    fn matches(&self, predicate: LogPredicate) -> bool;
}

impl<'a, 'tcx> AnalysisCtxt<'a, 'tcx> for CompilerCtxt<'a, 'tcx> {
    fn ctxt(self) -> CompilerCtxt<'a, 'tcx> {
        self
    }

    fn matches(&self, predicate: LogPredicate) -> bool {
        match predicate {
            LogPredicate::DebugBlock => false,
        }
    }
}

#[derive(Copy, Clone)]
pub(crate) struct WithCtxt<'a, 'tcx, T: Copy> {
    pub(crate) ctxt: CompilerCtxt<'a, 'tcx>,
    pub(crate) settings: &'a PcgSettings<'a>,
    pub(crate) extra_ctxt: T,
}

impl<'a, 'tcx, T: Copy> WithCtxt<'a, 'tcx, T> {
    pub(crate) fn new(ctxt: CompilerCtxt<'a, 'tcx>, extra_ctxt: T) -> Self {
        Self {
            ctxt,
            settings: &SETTINGS,
            extra_ctxt,
        }
    }
}

impl<'a, 'tcx> AnalysisCtxt<'a, 'tcx> for WithCtxt<'a, 'tcx, mir::BasicBlock> {
    fn ctxt(self) -> CompilerCtxt<'a, 'tcx> {
        self.ctxt
    }

    fn matches(&self, predicate: LogPredicate) -> bool {
        match predicate {
            LogPredicate::DebugBlock => {
                if let Some(debug_block) = self.settings.debug_block {
                    debug_block == self.extra_ctxt
                } else {
                    false
                }
            }
        }
    }
}
