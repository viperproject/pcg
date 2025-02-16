use std::collections::HashMap;
use std::fs;
use std::io;
use std::path::PathBuf;
use std::process::Command;

mod common;

const REGRESSION_THRESHOLD: f64 = 1.1;

fn build_release() {
    let status = Command::new("cargo")
        .args(["build", "--release"])
        .status()
        .expect("Failed to build release binary");

    assert!(status.success(), "Failed to build release binary");
}

fn extract_i_refs(output: &str) -> u64 {
    // Example line we're looking for: "==3770436== I refs:        58,812,310"
    for line in output.lines() {
        if line.contains("I refs:") {
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

fn read_previous_results(results_path: &PathBuf) -> io::Result<HashMap<String, u64>> {
    if !results_path.exists() {
        return Ok(HashMap::new());
    }

    let content = fs::read_to_string(results_path)?;
    let mut results = HashMap::new();

    for line in content.lines() {
        if let Some((file, value)) = line.split_once(": ") {
            if let Ok(value) = value.parse() {
                results.insert(file.to_string(), value);
            }
        }
    }

    Ok(results)
}

fn format_results(results: &[(String, u64)]) -> String {
    let mut output = String::new();
    for (file_name, i_refs) in results {
        output.push_str(&format!("{}: {}\n", file_name, i_refs));
    }
    output
}

#[cfg_attr(target_os = "macos", ignore)]
#[test]
fn benchmark_test_files() {
    // First build in release mode
    build_release();

    // Get the workspace directory and setup paths
    let workspace_dir = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());
    let test_dir = workspace_dir.join("test-files");
    let results_path = workspace_dir.join("benchmark_results.txt");

    let previous_results = read_previous_results(&results_path).unwrap_or_default();

    println!("\nBenchmark Results (I refs):");
    println!("==========================");

    let test_files = common::get_test_files(&test_dir);
    let mut results = Vec::with_capacity(test_files.len());
    let mut regression_detected = false;

    for test_file in &test_files {
        let file_name = test_file.file_name().unwrap().to_str().unwrap().to_string();
        println!("Benchmarking {}", file_name);

        let i_refs = run_cachegrind(&test_file);
        results.push((file_name.clone(), i_refs));

        if let Some(&prev_refs) = previous_results.get(&file_name) {
            let ratio = i_refs as f64 / prev_refs as f64;
            println!(
                "{}: {} (prev: {}, ratio: {:.2})",
                file_name, i_refs, prev_refs, ratio
            );

            if ratio > REGRESSION_THRESHOLD {
                println!(
                    "⚠️  PERFORMANCE REGRESSION for {}: ratio {:.2} exceeds threshold {:.2}",
                    file_name, ratio, REGRESSION_THRESHOLD
                );
                regression_detected = true;
            }
        } else {
            println!("{}: {} (first run)", file_name, i_refs);
        }
        println!(); // Add blank line for readability
    }

    println!("\nFinal Results:");
    println!("==============");
    print!("{}", format_results(&results));

    assert!(!regression_detected, "Performance regression detected!");
}
