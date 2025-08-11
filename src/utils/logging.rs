// use crate::rustc_interface::middle::mir::BasicBlock;
// use crate::utils::SnapshotLocation;

pub(crate) enum LogPredicate {
    DebugBlock,
}

#[macro_export]
macro_rules! log {
    ($predicate:expr, $ctxt:expr, $fmt:literal $(, $args:expr)*) => {
        {
            if $ctxt.matches($predicate) {
                tracing::info!($fmt $(, $args)*);
            }
        }
    };
}

pub(crate) use log;
