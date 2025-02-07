use serde_derive::Deserialize;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::io::Write;

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
pub fn run_pcg_on_crate_in_dir(dir: &Path) {
    let cwd = std::env::current_dir().unwrap();
    assert!(
        cfg!(debug_assertions),
        "Must be run in debug mode, to enable full checking"
    );
    let target = if cfg!(debug_assertions) {
        "debug"
    } else {
        "release"
    };
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
        .expect(&format!("Failed to execute cargo check on {}", dir.display()));

    assert!(
        exit.success(),
        "PCS check failed for directory {} with status: {}",
        dir.display(),
        exit
    );
}

#[allow(dead_code)]
pub fn run_pcg_on_file(file: &Path) {
    let workspace_dir = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());
    let pcs_exe = workspace_dir.join("target/debug/pcs_bin");
    println!("Running PCS on file: {}", file.display());

    let status = Command::new(&pcs_exe)
        .arg(file)
        .env("PCG_CHECK_ANNOTATIONS", "true")
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
pub fn run_on_crate(name: &str, version: &str) {
    match (name, version) {
        ("plotters", "0.3.7") => {
            // TODO: This should be relatively easy to fix
            eprintln!("Skipping plotters; haven't figured out how to run it on NixOS yet.");
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
    run_pcg_on_crate_in_dir(&dirname_path);
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
