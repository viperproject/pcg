use chrono::Local;
use derive_more::Deref;
use rayon::prelude::*;
use serde_derive::{Deserialize, Serialize};
use std::path::{Path, PathBuf};

mod common;
use common::{get, run_on_crate, RunOnCrateOptions, Target};

#[test]
#[ignore]
pub fn top_crates() {
    let parallelism = std::env::var("PCG_TEST_CRATE_PARALLELISM").unwrap_or("1".to_string());
    top_crates_parallel(500, Some("2025-03-13"), parallelism.parse().unwrap())
}

pub fn top_crates_parallel(n: usize, date: Option<&str>, parallelism: usize) {
    std::fs::create_dir_all("tmp").unwrap();
    rayon::ThreadPoolBuilder::new()
        .num_threads(parallelism)
        .build_global()
        .unwrap();
    let top_crates: Vec<_> = Crates::top(n, date).to_vec();
    top_crates
        .into_par_iter()
        .enumerate()
        .for_each(|(i, krate)| {
            let version = krate.version();
            println!("Starting: {i} ({})", krate.name);
            run_on_crate(
                &krate.name,
                version,
                date,
                RunOnCrateOptions::RunPCG {
                    target: Target::Release,
                    validity_checks: true,
                },
            );
            println!("Finished: {i} ({})", krate.name);
        });
}

/// A create on crates.io.
#[derive(Debug, Deserialize, Serialize, Clone)]
struct Crate {
    #[serde(rename = "id")]
    name: String,
    #[serde(rename = "max_stable_version")]
    version: Option<String>,
    #[serde(rename = "newest_version")]
    newest_version: String,
}

impl Crate {
    fn version(&self) -> &str {
        self.version.as_ref().unwrap_or(&self.newest_version)
    }
}

/// The list of crates from crates.io
#[derive(Debug, Deref, Deserialize)]
struct Crates {
    crates: Vec<Crate>,
}

const PAGE_SIZE: usize = 100;

fn download_crates(n: usize) -> Vec<Crate> {
    let mut all_crates = Vec::new();
    let mut page = 1;

    while all_crates.len() < n {
        let url = format!(
            "https://crates.io/api/v1/crates?page={}&per_page={PAGE_SIZE}&sort=downloads",
            page,
        );
        let resp = get(&url).expect("Could not fetch top crates");
        assert!(
            resp.status().is_success(),
            "Response status: {}",
            resp.status()
        );
        let page_crates = match serde_json::from_reader::<_, Crates>(resp) {
            Ok(page_crates) => page_crates,
            Err(e) => panic!("Invalid JSON {e}"),
        };
        assert_eq!(page_crates.crates.len(), PAGE_SIZE);
        all_crates.extend(page_crates.crates);
        page += 1;
    }

    all_crates
}

fn get_cache_path(date: &str) -> PathBuf {
    PathBuf::from("tests/top-crates").join(format!("{date}.json"))
}

fn read_from_cache(cache_path: &Path) -> Option<Vec<Crate>> {
    if let Ok(file) = std::fs::File::open(cache_path) {
        return Some(serde_json::from_reader::<_, Vec<Crate>>(file).unwrap());
    }
    None
}

fn write_to_cache(cache_path: PathBuf, crates: &[Crate]) {
    let file = std::fs::File::create(&cache_path).unwrap_or_else(|err| {
        panic!(
            "Failed to create cache file {}: {}",
            cache_path.display(),
            err
        );
    });
    serde_json::to_writer(file, &crates).unwrap();
}

impl Crates {
    pub fn top(n: usize, date: Option<&str>) -> Crates {
        let today = Local::now().format("%Y-%m-%d").to_string();
        let date = date.unwrap_or(today.as_str());
        let cache_path = get_cache_path(date);
        let crates = read_from_cache(&cache_path).unwrap_or_else(|| {
            assert_eq!(
                date,
                today,
                "Cannot get crates from {} because we JSON file {} doesn't exist",
                date,
                cache_path.display()
            );
            let crates = download_crates(n);
            write_to_cache(cache_path, &crates);
            crates
        });
        assert!(
            crates.len() >= n,
            "Tried to get {} crates but only had {}",
            n,
            crates.len()
        );
        Crates {
            crates: crates[..n].to_vec(),
        }
    }
}
