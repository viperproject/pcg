use serde_derive::Deserialize;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

#[allow(dead_code)]
pub fn get(url: &str) -> reqwest::Result<reqwest::blocking::Response> {
    println!("Getting: {url}");
    reqwest::blocking::ClientBuilder::new()
        .user_agent("Rust Corpus - Top Crates Scrapper")
        .build()?
        .get(url)
        .send()
}

#[allow(dead_code)]
pub fn get_rust_toolchain_channel() -> String {
    #[derive(Deserialize)]
    struct RustToolchainFile {
        toolchain: RustToolchain,
    }

    #[derive(Deserialize)]
    struct RustToolchain {
        channel: String,
        #[allow(dead_code)]
        components: Option<Vec<String>>,
    }

    let content = include_str!("../../rust-toolchain");
    // Be ready to accept TOML format
    // See: https://github.com/rust-lang/rustup/pull/2438
    if content.starts_with("[toolchain]") {
        let rust_toolchain: RustToolchainFile =
            toml::from_str(content).expect("failed to parse rust-toolchain file");
        rust_toolchain.toolchain.channel
    } else {
        content.trim().to_string()
    }
}

#[allow(dead_code)]
pub fn run_pcg_on_crate_in_dir(dir: &Path, debug: bool) {
    let cwd = std::env::current_dir().unwrap();
    let cargo_build = Command::new("cargo")
        .arg("build")
        .args(if !debug { vec!["--release"] } else { vec![] })
        .current_dir(&cwd)
        .status()
        .expect("Failed to build pcs_bin");

    assert!(cargo_build.success(), "Failed to build pcs_bin");
    let target = if debug { "debug" } else { "release" };
    let cargo = "cargo";
    let pcs_exe = cwd.join(["target", target, "pcs_bin"].iter().collect::<PathBuf>());
    println!("Running PCS on directory: {}", dir.display());
    let exit = Command::new(cargo)
        .arg("check")
        .env("RUST_TOOLCHAIN", get_rust_toolchain_channel())
        .env("RUSTUP_TOOLCHAIN", get_rust_toolchain_channel())
        .env("RUSTC", &pcs_exe)
        .current_dir(dir)
        .status()
        .unwrap_or_else(|_| panic!("Failed to execute cargo check on {}",
            dir.display()));

    assert!(
        exit.success(),
        "PCS check failed for directory {} with status: {}",
        dir.display(),
        exit
    );
}

pub fn is_polonius_test_file(file: &Path) -> bool {
    file.to_str().unwrap().contains("polonius")
}

#[allow(dead_code)]
pub fn run_pcg_on_file(file: &Path) {
    let workspace_dir = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());
    let pcs_exe = workspace_dir.join("target/debug/pcs_bin");
    println!("Running PCG on file: {}", file.display());

    let status = Command::new(&pcs_exe)
        .arg(file)
        .env("PCG_CHECK_ANNOTATIONS", "true")
        .env(
            "PCG_POLONIUS",
            if is_polonius_test_file(file) {
                "true"
            } else {
                "false"
            },
        )
        .status()
        .unwrap_or_else(|e| panic!("Failed to execute test {}: {}", file.display(), e));

    assert!(
        status.success(),
        "Test {} failed with status: {}",
        file.display(),
        status
    );
}

#[allow(dead_code)]
pub fn run_on_crate(name: &str, version: &str, debug: bool) {
    match (name, version) {
        ("ring", "0.17.3") => {
            eprintln!("Skipping ring; it doesn't compile for some reason.");
            return;
        }
        ("generic-array", "1.2.0") if rustversion::cfg!(nightly(2024 - 09 - 14)) => {
            eprintln!("Skipping generic-array; it's not supported on nightly 2024-09-14");
            return;
        }
        ("plotters", "0.3.7") | ("clang-sys", "1.8.1") => {
            // TODO: This should be relatively easy to fix
            eprintln!("Skipping {name} {version}; haven't figured out how to run it on NixOS yet.");
            return;
        }
        ("darling", "0.20.10") | ("tokio-native-tls", "0.3.1") => {
            eprintln!(
                r#"Skipping {name} {version}; it will not compile due to an old dependency of proc_macro.
            For more information see: https://github.com/rust-lang/rust/issues/113152
            "#
            );
            return;
        }
        ("derive_more", _) => {
            eprintln!("Skipping derive_more; compilation requires enabling a feature.");
            return;
        }
        ("winreg", _) => {
            eprintln!("Skipping winreg; it's for Windows only.");
            return;
        }
        ("criterion-plot", "0.5.0") => {
            eprintln!("Skipping criterion-plot; it returns an error: error: unexpected `cfg` condition value: `cargo-clippy`");
            return;
        }
        ("tiny-keccak", "2.0.2") => {
            eprintln!("Skipping tiny-keccak; compilation requires choosing a hash function");
            return;
        }
        ("redox_users", _) => {
            eprintln!("Skipping redox_users; it's for Redox OS only.");
            return;
        }
        ("Inflector", _) => {
            eprintln!("Skipping Inflector; it doesn't compile (probably too old).");
            return;
        }
        _ => {}
    }
    let dirname = format!("./tmp/{name}-{version}");
    let filename = format!("{dirname}.crate");
    if !std::path::PathBuf::from(&filename).exists() {
        let dl = format!("https://crates.io/api/v1/crates/{name}/{version}/download");
        let mut resp = get(&dl).expect("Could not fetch top crates");
        let mut file = std::fs::File::create(&filename).unwrap();
        resp.copy_to(&mut file).unwrap();
    }
    println!("Unwrapping: {filename}");
    let status = Command::new("tar")
        .args(["-xf", &filename, "-C", "./tmp/"])
        .status()
        .unwrap();
    assert!(status.success());
    let mut file = std::fs::OpenOptions::new()
        .write(true)
        .append(true)
        .open(format!("{dirname}/Cargo.toml"))
        .unwrap();
    writeln!(file, "\n[workspace]").unwrap();
    let dirname_path = PathBuf::from(&dirname);
    run_pcg_on_crate_in_dir(&dirname_path, debug);
    std::fs::remove_dir_all(dirname).unwrap();
}

#[allow(dead_code)]
pub fn get_test_files(test_dir: &Path) -> Vec<PathBuf> {
    let mut test_files: Vec<_> = std::fs::read_dir(test_dir)
        .unwrap()
        .filter_map(|entry| {
            let entry = entry.unwrap();
            let path = entry.path();
            let file_name = path.file_name()?.to_str()?;
            if file_name.chars().next()?.is_ascii_digit() && file_name.ends_with(".rs") {
                Some(path)
            } else {
                None
            }
        })
        .collect();

    // Sort test files by name
    test_files.sort();
    test_files
}
