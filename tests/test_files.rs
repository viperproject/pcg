#[allow(unused)]
use rayon::prelude::*;
use std::path::PathBuf;

mod common;

#[test]
fn check_test_files() {
    // Get the workspace directory from CARGO_MANIFEST_DIR
    let workspace_dir = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());

    // Find all numbered test files
    let test_dir = workspace_dir.join("test-files");

    let mut test_files = common::get_test_files(&test_dir);

    test_files.sort_by(|a, b| {
        let a_lines = std::fs::read_to_string(a).unwrap().lines().count();
        let b_lines = std::fs::read_to_string(b).unwrap().lines().count();
        a_lines.cmp(&b_lines)
    });

    // test_files.par_iter().panic_fuse().for_each(|test_file| {
    //     common::run_pcg_on_file(test_file);
    // });

    test_files.iter().for_each(|test_file| {
        common::run_pcg_on_file(test_file);
    });
}
