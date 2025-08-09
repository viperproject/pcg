use crate::rustc_interface::middle::mir::BasicBlock;
use crate::utils::SnapshotLocation;

/// Extracts the BasicBlock from a SnapshotLocation
pub(crate) fn get_block_from_location(loc: SnapshotLocation) -> BasicBlock {
    match loc {
        SnapshotLocation::Before(analysis_loc) => analysis_loc.location.block,
        SnapshotLocation::After(block) => block,
        SnapshotLocation::Loop(block) => block,
        SnapshotLocation::BeforeJoin(block) => block,
        SnapshotLocation::BeforeRefReassignment(location) => location.block,
    }
}

/// Conditional logging macro that filters based on PCG_DEBUG_BLOCK environment variable
///
/// Usage: log!(location, "format string", args...)
///
/// If PCG_DEBUG_BLOCK is set, only logs if the block in the location matches the debug block.
/// If PCG_DEBUG_BLOCK is not set, always logs.
#[macro_export]
macro_rules! log {
    ($loc:expr, $fmt:literal $(, $args:expr)*) => {
        {
            use $crate::utils::logging::get_block_from_location;
            use $crate::utils::PCG_DEBUG_BLOCK;

            let location = $loc;
            let block = get_block_from_location(location);

            // Only log if PCG_DEBUG_BLOCK is not set, or if it matches the current block
            if PCG_DEBUG_BLOCK.is_none() || PCG_DEBUG_BLOCK.as_ref() == Some(&block) {
                tracing::info!("[{:?}] {}", location, format!($fmt $(, $args)*));
            }
        }
    };
}
