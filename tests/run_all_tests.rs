#[test]
fn run_all_tests() {
    use std::path::PathBuf;
    use std::process::Command;

    // Get the workspace directory from CARGO_MANIFEST_DIR
    let workspace_dir = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());

    // Find all numbered test files
    let test_dir = workspace_dir.join("tests");
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

    // Get the path to our executable
    let pcs_exe = workspace_dir.join("target/debug/pcs_bin");

    // Run each test file
    for test_file in test_files {
        println!("Running test: {}", test_file.display());

        let status = Command::new(&pcs_exe)
            .arg(&test_file)
            .status()
            .unwrap_or_else(|e| panic!("Failed to execute test {}: {}", test_file.display(), e));

        assert!(
            status.success(),
            "Test {} failed with status: {}",
            test_file.display(),
            status
        );
    }
}
