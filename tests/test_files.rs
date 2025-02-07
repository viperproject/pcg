use std::path::PathBuf;
mod test_utils;

#[test]
fn check_test_files() {
    // Get the workspace directory from CARGO_MANIFEST_DIR
    let workspace_dir = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());

    // Find all numbered test files
    let test_dir = workspace_dir.join("test-files");
    let mut test_files: Vec<_> = std::fs::read_dir(&test_dir)
        .unwrap()
        .filter_map(|entry| {
            let entry = entry.unwrap();
            let path = entry.path();
            let file_name = path.file_name()?.to_str()?;
            // Match files that start with numbers and end with .rs
            // Exclude .wip files
            if file_name.chars().next()?.is_ascii_digit() && file_name.ends_with(".rs") {
                Some(path)
            } else {
                None
            }
        })
        .collect();

    // Sort test files by name to ensure consistent order
    test_files.sort();

    // Run each test file
    for test_file in test_files {
        test_utils::run_pcs_on_file(&test_file);
    }
}
