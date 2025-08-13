use crate::borrow_checker::BorrowCheckerInterface;
use crate::pcg::{PcgArena, SymbolicCapabilityCtxt};
use crate::rustc_interface::middle::{mir, ty};
use crate::utils::logging::LogPredicate;
use crate::utils::{CompilerCtxt, HasBorrowCheckerCtxt, HasCompilerCtxt, PcgSettings, SETTINGS};

#[derive(Copy, Clone)]
pub(crate) struct AnalysisCtxt<'a, 'tcx> {
    pub(crate) ctxt: CompilerCtxt<'a, 'tcx>,
    pub(crate) settings: &'a PcgSettings<'a>,
    pub(crate) symbolic_capability_ctxt: SymbolicCapabilityCtxt<'a>,
    pub(crate) block: Option<mir::BasicBlock>,
    pub(crate) arena: PcgArena<'a>,
}

impl<'a> AnalysisCtxt<'a, '_> {
    pub(crate) fn alloc<T>(&self, val: T) -> &'a mut T {
        self.arena.alloc(val)
    }
}

impl<'a, 'tcx> HasCompilerCtxt<'a, 'tcx> for AnalysisCtxt<'a, 'tcx> {
    fn ctxt(&self) -> CompilerCtxt<'a, 'tcx, ()> {
        self.ctxt.ctxt()
    }
}

impl<'a, 'tcx> HasBorrowCheckerCtxt<'a, 'tcx> for AnalysisCtxt<'a, 'tcx> {
    fn bc(&self) -> &'a dyn BorrowCheckerInterface<'tcx> {
        self.ctxt.bc()
    }

    fn bc_ctxt(&self) -> CompilerCtxt<'a, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>> {
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
    pub(crate) fn new(
        ctxt: CompilerCtxt<'a, 'tcx>,
        block: Option<mir::BasicBlock>,
        symbolic_capability_ctxt: SymbolicCapabilityCtxt<'a>,
        arena: PcgArena<'a>,
    ) -> Self {
        Self {
            ctxt,
            settings: &SETTINGS,
            block,
            symbolic_capability_ctxt,
            arena,
        }
    }
    pub(crate) fn matches(&self, predicate: LogPredicate) -> bool {
        match predicate {
            LogPredicate::DebugBlock => {
                if let Some(debug_block) = self.settings.debug_block {
                    debug_block == self.block.unwrap()
                } else {
                    false
                }
            }
        }
    }
}
