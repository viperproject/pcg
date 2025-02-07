use std::path::PathBuf;
use std::process::Command;
use std::collections::HashMap;

mod common;

fn build_release() {
    let status = Command::new("cargo")
        .args(["build", "--release"])
        .status()
        .expect("Failed to build release binary");

    assert!(status.success(), "Failed to build release binary");
}

fn extract_i_refs(output: &str) -> u64 {
    // Example line we're looking for: "I   refs:      2,859,668"
    for line in output.lines() {
        if line.trim().starts_with("I   refs:") {
            return line
                .split_whitespace()
                .last()
                .unwrap()
                .replace(",", "")
                .parse()
                .expect("Failed to parse I refs value");
        }
    }
    panic!("Could not find I refs in valgrind output {}", output);
}

fn run_cachegrind(file_path: &PathBuf) -> u64 {
    let output = Command::new("valgrind")
        .args([
            "--tool=cachegrind",
            "target/release/pcs_bin",
            file_path.to_str().unwrap(),
        ])
        .output()
        .expect("Failed to run valgrind");

    let stderr = String::from_utf8_lossy(&output.stderr);
    extract_i_refs(&stderr)
}

#[test]
fn benchmark_test_files() {
    // First build in release mode
    build_release();

    // Get the workspace directory
    let workspace_dir = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());
    let test_dir = workspace_dir.join("test-files");

    let test_files = common::get_test_files(&test_dir);
    // Run benchmarks and collect results
    let mut results = HashMap::new();

    for test_file in test_files {
        let file_name = test_file.file_name().unwrap().to_str().unwrap().to_string();
        println!("Benchmarking {}", file_name);

        let i_refs = run_cachegrind(&test_file);
        results.insert(file_name, i_refs);
    }

    // Print results
    println!("\nBenchmark Results (I refs):");
    println!("==========================");
    for (file, i_refs) in &results {
        println!("{}: {}", file, i_refs);
    }
}
