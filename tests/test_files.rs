use rayon::prelude::*;
use std::path::PathBuf;

mod common;

#[test]
fn check_test_files() {
    // Get the workspace directory from CARGO_MANIFEST_DIR
    let workspace_dir = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());

    // Find all numbered test files
    let test_dir = workspace_dir.join("test-files");

    let test_files = common::get_test_files(&test_dir);

    test_files.par_iter().for_each(|test_file| {
        common::run_pcg_on_file(test_file);
    });
}
