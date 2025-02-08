use serde_derive::{Deserialize, Serialize};

mod common;
use common::{get, run_on_crate};

#[test]
pub fn top_crates() {
    top_crates_range(34..500)
}

pub fn top_crates_range(range: std::ops::Range<usize>) {
    std::fs::create_dir_all("tmp").unwrap();
    let top_crates = CratesIter::top(range);
    for (i, krate) in top_crates {
        let version = krate.version.unwrap_or(krate.newest_version);
        println!("Starting: {i} ({})", krate.name);
        run_on_crate(&krate.name, &version);
    }
}

/// A create on crates.io.
#[derive(Debug, Deserialize, Serialize)]
struct Crate {
    #[serde(rename = "id")]
    name: String,
    #[serde(rename = "max_stable_version")]
    version: Option<String>,
    #[serde(rename = "newest_version")]
    newest_version: String,
}

/// The list of crates from crates.io
#[derive(Debug, Deserialize)]
struct CratesList {
    crates: Vec<Crate>,
}

const PAGE_SIZE: usize = 100;
struct CratesIter {
    curr_idx: usize,
    curr_page: usize,
    crates: Vec<Crate>,
}

impl CratesIter {
    pub fn new(start: usize) -> Self {
        Self {
            curr_idx: start,
            curr_page: start / PAGE_SIZE + 1,
            crates: Vec::new(),
        }
    }
    pub fn top(range: std::ops::Range<usize>) -> impl Iterator<Item = (usize, Crate)> {
        Self::new(range.start).take(range.len())
    }
}

impl Iterator for CratesIter {
    type Item = (usize, Crate);
    fn next(&mut self) -> Option<Self::Item> {
        if self.crates.is_empty() {
            let url = format!(
                "https://crates.io/api/v1/crates?page={}&per_page={PAGE_SIZE}&sort=downloads",
                self.curr_page,
            );
            let resp = get(&url).expect("Could not fetch top crates");
            assert!(
                resp.status().is_success(),
                "Response status: {}",
                resp.status()
            );
            let page_crates: CratesList = match serde_json::from_reader(resp) {
                Ok(page_crates) => page_crates,
                Err(e) => panic!("Invalid JSON {e}"),
            };
            assert_eq!(page_crates.crates.len(), PAGE_SIZE);
            self.crates = page_crates.crates;
            self.crates.reverse();
            self.crates
                .truncate(self.crates.len() - self.curr_idx % PAGE_SIZE);
            self.curr_page += 1;
        }
        self.curr_idx += 1;
        Some((self.curr_idx - 1, self.crates.pop().unwrap()))
    }
}
