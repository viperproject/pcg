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
pub fn cargo_clean_in_dir(dir: &Path) {
    let cargo_clean = Command::new("cargo")
        .arg("clean")
        .current_dir(dir)
        .status()
        .unwrap_or_else(|_| panic!("Failed to clean cargo in {}", dir.display()));
    assert!(
        cargo_clean.success(),
        "Failed to clean cargo in {}",
        dir.display()
    );
}

#[allow(dead_code)]
#[must_use]
pub fn run_pcg_on_crate_in_dir(dir: &Path, options: RunOnCrateOptions) -> bool {
    let cwd = std::env::current_dir().unwrap();
    let build_args = match options.target() {
        Target::Release => vec!["--release"],
        Target::Debug => vec![],
    };
    let cargo_build = Command::new("cargo")
        .arg("build")
        .args(build_args)
        .current_dir(&cwd)
        .status()
        .expect("Failed to build pcg_bin");

    assert!(cargo_build.success(), "Failed to build pcg_bin");
    let target = if matches!(options.target(), Target::Release) {
        "release"
    } else {
        "debug"
    };
    let pcs_exe = cwd.join(["target", target, "pcg_bin"].iter().collect::<PathBuf>());
    println!("Running PCG on directory: {}", dir.display());
    let mut command = Command::new("cargo");
    command
        .arg("check")
        .current_dir(dir)
        .env("RUST_TOOLCHAIN", get_rust_toolchain_channel())
        .env("RUSTUP_TOOLCHAIN", get_rust_toolchain_channel())
        .env(
            "PCG_VALIDITY_CHECKS",
            format!("{}", options.validity_checks()),
        )
        .env("RUSTC", &pcs_exe);
    for (key, value) in options.extra_env_vars() {
        command.env(key, value);
    }
    if let Some(function) = options.function() {
        command.env("PCG_CHECK_FUNCTION", function);
    }
    let exit = command
        .status()
        .unwrap_or_else(|_| panic!("Failed to execute cargo check on {}", dir.display()));

    exit.success()
}

pub fn is_polonius_test_file(file: &Path) -> bool {
    file.to_str().unwrap().contains("polonius")
}

#[allow(dead_code)]
pub fn run_pcg_on_file(file: &Path) {
    let workspace_dir = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());
    let pcs_exe = workspace_dir.join("target/debug/pcg_bin");
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

pub fn crate_download_dirname(name: &str, version: &str) -> String {
    format!("./tmp/{name}-{version}")
}

pub fn is_supported_crate(name: &str, version: &str) -> Result<(), String> {
    match (name, version) {
        ("rustls", "0.23.23") => {
            // When we ran the original evaluation for some reason rustls didn't compile
            // It's fixed now, but we skip it to get the same results
            Err("skipped because we didn't run in original evaluation ".to_string())
        }
        ("system-configuration", "0.6.1") => {
            Err("Skipping system-configuration; it doesn't compile.".to_string())
        }
        ("ascii", "1.1.0") => {
            Err("Skipping ascii; it doesn't compile.".to_string())
        }
        ("net2", "0.2.39") => {
            Err("Skipping net2; this version doesn't compile.".to_string())
        }
        ("plotters", "0.3.7") | ("clang-sys", "1.8.1") => {
            // TODO: This should be relatively easy to fix
            Err("Skipping {name} {version}; haven't figured out how to run it on NixOS yet.".to_string())
        }
        ("darling", "0.20.10") | ("tokio-native-tls", "0.3.1") => {
            Err(format!(
                r#"Skipping {name} {version}; it will not compile due to an old dependency of proc_macro.
            For more information see: https://github.com/rust-lang/rust/issues/113152
            "#
            ))
        }
        ("derive_more", _) => {
            Err("Skipping derive_more; compilation requires enabling a feature.".to_string())
        }
        ("winreg", _) => {
            Err("Skipping winreg; it's for Windows only.".to_string())
        }
        ("criterion-plot", "0.5.0") => {
            Err("Skipping criterion-plot; it returns an error: error: unexpected `cfg` condition value: `cargo-clippy`".to_string())
        }
        ("tiny-keccak", "2.0.2") => {
            Err("Skipping tiny-keccak; compilation requires choosing a hash function".to_string())
        }
        ("redox_users", _) => {
            Err("Skipping redox_users; it's for Redox OS only.".to_string())
        }
        ("Inflector", _) => {
            Err("Skipping Inflector; it doesn't compile (probably too old).".to_string())
        }
        _ => Ok(()),
    }
}

pub fn cached_cargo_lock_file(name: &str, version: &str, date: &str) -> PathBuf {
    PathBuf::from(format!("tests/top-crates/{date}/{name}-{version}.lock"))
}

pub fn download_crate(name: &str, version: &str, date: Option<&str>) -> PathBuf {
    let dirname = crate_download_dirname(name, version);
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
    if let Some(date) = date {
        let cargo_lock_file = cached_cargo_lock_file(name, version, date);
        if cargo_lock_file.exists() {
            eprintln!("Using cached Cargo.lock for {name} {version}");
            std::fs::copy(&cargo_lock_file, format!("{dirname}/Cargo.lock")).unwrap();
        } else {
            eprintln!("No cached Cargo.lock {}", cargo_lock_file.display());
        }
    }
    PathBuf::from(&dirname)
}

#[allow(dead_code)]
#[derive(Debug, Clone, Copy)]
pub enum Target {
    Debug,
    Release,
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
pub enum RunOnCrateOptions {
    TypecheckOnly {
        extra_env_vars: Vec<(String, String)>,
    },
    RunPCG {
        target: Target,
        validity_checks: bool,
        function: Option<&'static str>,
        extra_env_vars: Vec<(String, String)>,
    },
}

impl RunOnCrateOptions {
    pub fn function(&self) -> Option<&'static str> {
        match self {
            RunOnCrateOptions::RunPCG { function, .. } => *function,
            RunOnCrateOptions::TypecheckOnly { .. } => None,
        }
    }

    pub fn extra_env_vars(&self) -> &[(String, String)] {
        match self {
            RunOnCrateOptions::RunPCG { extra_env_vars, .. } => extra_env_vars,
            RunOnCrateOptions::TypecheckOnly { extra_env_vars } => extra_env_vars,
        }
    }

    pub fn validity_checks(&self) -> bool {
        match self {
            RunOnCrateOptions::RunPCG {
                validity_checks, ..
            } => *validity_checks,
            RunOnCrateOptions::TypecheckOnly { .. } => false,
        }
    }

    pub fn target(&self) -> Target {
        match self {
            RunOnCrateOptions::RunPCG { target, .. } => *target,
            RunOnCrateOptions::TypecheckOnly { .. } => Target::Release,
        }
    }
}

pub enum RunOnCrateResult {
    Success,
    Skipped,
    Failed
}

#[must_use]
pub fn run_on_crate(
    name: &str,
    version: &str,
    date: Option<&str>,
    options: RunOnCrateOptions,
) -> RunOnCrateResult {
    if let Err(e) = is_supported_crate(name, version) {
        eprintln!("{e}");
        return RunOnCrateResult::Skipped;
    }
    let dirname = download_crate(name, version, date);
    let result = run_pcg_on_crate_in_dir(&dirname, options);
    if let Some(date) = date {
        let cargo_lock_file = cached_cargo_lock_file(name, version, date);
        if !cargo_lock_file.exists() {
            std::fs::copy(dirname.join("Cargo.lock"), &cargo_lock_file).unwrap();
        }
    }
    std::fs::remove_dir_all(&dirname).unwrap_or_else(|e| {
        panic!("Failed to remove directory {}: {}", dirname.display(), e);
    });
    if result {
        RunOnCrateResult::Success
    } else {
        RunOnCrateResult::Failed
    }
}

#[allow(dead_code)]
pub fn ensure_successful_run_on_crate(
    name: &str,
    version: &str,
    date: Option<&str>,
    options: RunOnCrateOptions,
) {
    let result = run_on_crate(name, version, date, options);
    assert!(matches!(result, RunOnCrateResult::Success), "PCG check failed for crate {name} {version}");
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
