mod common;

#[test]
fn test_selected_crates() {
    // Create tmp directory if it doesn't exist
    std::fs::create_dir_all("tmp").unwrap();

    // common::run_on_crate("ascii", "1.1.0", true);
    // common::run_on_crate("cc", "1.2.16", true);
    // common::run_on_crate("crc", "3.2.1", true);
    // common::run_on_crate("cookie", "0.18.1", Some("2025-03-13"), false, true);
    // common::run_on_crate("futures-util", "0.3.31", false);
    // common::run_on_crate("gimli", "0.31.1", false);
    // common::run_on_crate(
    //     "hashbrown",
    //     "0.15.2",
    //     Some("2025-03-13"),
    //     common::RunOnCrateOptions::RunPCG {
    //         target: common::Target::Release,
    //         validity_checks: true,
    //     },
    // );
    // common::run_on_crate("http", "1.2.0", true);
    // common::run_on_crate("miniz_oxide", "0.8.5", true);
    // common::run_on_crate("num-conv", "0.1.0", true);
    // common::run_on_crate("num_enum", "0.7.3", true);
    // common::run_on_crate("proc-macro2", "1.0.93", false);
    // common::run_on_crate("radium", "1.1.0", true);
    // common::run_on_crate("regex-automata", "0.4.9", true);
    // common::run_on_crate("ring", "0.17.3", true);
    // common::run_on_crate("serde_with", "3.12.0", true);
    // common::run_on_crate("tap", "1.0.1", false);

    // common::run_on_crate(
    //     "serde_json",
    //     "1.0.140",
    //     Some("2025-03-13"),
    //     common::RunOnCrateOptions::RunPCG {
    //         target: common::Target::Release,
    //         validity_checks: true,
    //     },
    // );

    // We should test this consistently because it's a good loop test
    // common::run_on_crate(
    //     "tinytemplate",
    //     "1.2.1",
    //     Some("2025-03-13"),
    //     common::RunOnCrateOptions::RunPCG {
    //         target: common::Target::Release,
    //         validity_checks: false,
    //     },
    // );

    // common::run_on_crate(
    //     "serde_derive",
    //     "1.0.219",
    //     Some("2025-03-13"),
    //     common::RunOnCrateOptions::RunPCG {
    //         target: common::Target::Debug,
    //         validity_checks: false,
    //     },
    // );

    // common::run_on_crate(
    //     "regex-syntax",
    //     "0.8.5",
    //     Some("2025-03-13"),
    //     common::RunOnCrateOptions::RunPCG {
    //         target: common::Target::Debug,
    //         validity_checks: true,
    //     },
    // );

    // common::run_on_crate(
    //     "crossbeam-deque",
    //     "0.8.6",
    //     None,
    //     common::RunOnCrateOptions::RunPCG {
    //         target: common::Target::Release,
    //         validity_checks: false,
    //     },
    // );

    // common::run_on_crate(
    //     "itertools",
    //     "0.14.0",
    //     None,
    //     common::RunOnCrateOptions::RunPCG {
    //         target: common::Target::Release,
    //         validity_checks: false,
    //     },
    // );

    // common::run_on_crate(
    //     "opentelemetry",
    //     "0.28.0",
    //     None,
    //     common::RunOnCrateOptions::RunPCG {
    //         target: common::Target::Release,
    //         validity_checks: false,
    //     },
    // );

    // common::run_on_crate(
    //     "syn",
    //     "2.0.100",
    //     Some("2025-03-13"),
    //     common::RunOnCrateOptions::RunPCG {
    //         target: common::Target::Release,
    //         validity_checks: true,
    //     },
    // );

    // common::run_on_crate(
    //     "cfg-if",
    //     "1.0.0",
    //     Some("2025-03-13"),
    //     common::RunOnCrateOptions::RunPCG {
    //         target: common::Target::Release,
    //         validity_checks: false,
    //     },
    // );

    // common::run_on_crate("toml_edit", "0.22.23", false);
    // common::run_on_crate("tonic", "0.12.3", true);
    // common::run_on_crate("wasm-bindgen-backend", "0.2.100", true);
    // common::run_on_crate("zerovec-derive", "0.10.3", Some("2025-03-13"), true, false);
    // common::run_on_crate("zerocopy-derive", "0.8.23", Some("2025-03-13"), common::RunOnCrateOptions::RunPCG {
    //     target: common::Target::Debug,
    //     validity_checks: false,
    // });
}
