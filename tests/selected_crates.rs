mod common;

#[test]
fn test_selected_crates() {
    // Create tmp directory if it doesn't exist
    std::fs::create_dir_all("tmp").unwrap();

    common::ensure_successful_run_on_crate(
        "pest",
        "2.7.15",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: false,
            function: None,
            extra_env_vars: vec![],
        },
    );

    common::ensure_successful_run_on_crate(
        "idna",
        "1.0.3",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: false,
            function: None,
            extra_env_vars: vec![],
        },
    );

    common::ensure_successful_run_on_crate(
        "chrono",
        "0.4.40",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: false,
            function: Some("format::scan::timezone_offset_2822"),
            extra_env_vars: vec![],
        },
    );

    // common::ensure_successful_run_on_crate(
    //     "bindgen",
    //     "0.71.1",
    //     Some("2025-03-13"),
    //     common::RunOnCrateOptions::RunPCG {
    //         target: common::Target::Debug,
    //         validity_checks: false,
    //         function: None,
    //         extra_env_vars: vec![(
    //             "PCG_SKIP_FUNCTION".to_string(),
    //             "<ir::comp::CompInfo as codegen::CodeGenerator>::codegen".to_string(),
    //         )],
    //     },
    // );

    // Polonius also works, checking variable liveness alone isn't sufficient
    // for determining if a lifetime projection is live at a point.
    #[cfg(feature = "custom-rust-toolchain")]
    common::ensure_successful_run_on_crate(
        "yaml-rust",
        "0.4.5",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("parser::Parser::<T>::stream_start"),
            extra_env_vars: vec![],
        },
    );

    let _warn_only_vars = vec![(
        "PCG_VALIDITY_CHECKS_WARN_ONLY".to_string(),
        "true".to_string(),
    )];

    let _visualization_env_vars = vec![
        (
            "PCG_VISUALIZATION_DATA_DIR".to_string(),
            "../../visualization/data".to_string(),
        ),
        ("PCG_VISUALIZATION".to_string(), "true".to_string()),
    ];


    common::ensure_successful_run_on_crate(
        "flate2",
        "1.1.0",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("<gz::write::MultiGzDecoder<W> as std::io::Write>::write"),
            extra_env_vars: vec![],
        },
    );

    common::ensure_successful_run_on_crate(
        "pest",
        "2.7.15",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("parser_state::ParserState::<'i, R>::match_char_by"),
            extra_env_vars: vec![],
        },
    );

    common::ensure_successful_run_on_crate(
        "linked-hash-map",
        "0.5.6",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("LinkedHashMap::<K, V, S>::get_refresh"),
            extra_env_vars: vec![],
        },
    );

    common::ensure_successful_run_on_crate(
        "serde_yaml",
        "0.9.34+deprecated",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("libyaml::emitter::Emitter::<'a>::flush"),
            extra_env_vars: vec![],
        },
    );

    // common::ensure_successful_run_on_crate(
    //     "brotli-decompressor",
    //     "4.0.2",
    //     Some("2025-03-13"),
    //     common::RunOnCrateOptions::RunPCG {
    //         target: common::Target::Debug,
    //         validity_checks: true,
    //         function: Some("<MemPool<'a, T> as core::default::Default>::default"),
    //         extra_env_vars: vec![],
    //     },
    // );

    common::ensure_successful_run_on_crate(
        "predicates-tree",
        "1.0.12",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: None,
            extra_env_vars: vec![],
        },
    );

    common::ensure_successful_run_on_crate(
        "concurrent-queue",
        "2.5.0",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: None,
            extra_env_vars: vec![],
        },
    );

    // common::ensure_successful_run_on_crate(
    //     "encoding_rs",
    //     "0.8.35",
    //     Some("2025-03-13"),
    //     common::RunOnCrateOptions::RunPCG {
    //         target: common::Target::Debug,
    //         validity_checks: true,
    //         function: None,
    //         extra_env_vars: vec![],
    //     },
    // );

    common::ensure_successful_run_on_crate(
        "encoding_rs",
        "0.8.35",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: false,
            function: Some("shift_jis::ShiftJisEncoder::encode_from_utf16_raw"),
            extra_env_vars: vec![],
        },
    );

    common::ensure_successful_run_on_crate(
        "cc",
        "1.2.16",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: false,
            function: Some("flags::RustcCodegenFlags::<'this>::cc_flags"),
            extra_env_vars: vec![],
        },
    );

    common::ensure_successful_run_on_crate(
        "encoding_rs",
        "0.8.35",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: false,
            function: Some("iso_2022_jp::Iso2022JpDecoder::decode_to_utf16_raw"),
            extra_env_vars: vec![],
        },
    );

    // common::ensure_successful_run_on_crate(
    //     "encoding_rs",
    //     "0.8.35",
    //     Some("2025-03-13"),
    //     common::RunOnCrateOptions::RunPCG {
    //         target: common::Target::Debug,
    //         validity_checks: false,
    //         function: None,
    //         extra_env_vars: vec![],
    //     },
    // );

    common::ensure_successful_run_on_crate(
        "serde_derive",
        "1.0.219",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: false,
            function: Some("internals::attr::parse_lit_into_path"),
            extra_env_vars: vec![],
        },
    );

    common::ensure_successful_run_on_crate(
        "serde_derive",
        "1.0.219",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: false,
            function: Some("internals::attr::is_cow"),
            extra_env_vars: vec![],
        },
    );

    common::ensure_successful_run_on_crate(
        "serde_derive",
        "1.0.219",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: false,
            function: Some("internals::ast::Container::<'a>::from_ast"),
            extra_env_vars: vec![],
        },
    );

    // common::ensure_successful_run_on_crate("ascii", "1.1.0", true);
    // common::ensure_successful_run_on_crate("cc", "1.2.16", true);
    // common::ensure_successful_run_on_crate("crc", "3.2.1", true);
    // common::ensure_successful_run_on_crate("cookie", "0.18.1", Some("2025-03-13"), false, true);
    // common::ensure_successful_run_on_crate("futures-util", "0.3.31", false);
    // common::ensure_successful_run_on_crate("gimli", "0.31.1", false);
    // common::ensure_successful_run_on_crate(
    //     "hashbrown",
    //     "0.15.2",
    //     Some("2025-03-13"),
    //     common::RunOnCrateOptions::RunPCG {
    //         target: common::Target::Release,
    //         validity_checks: true,
    //     },
    // );
    // common::ensure_successful_run_on_crate("http", "1.2.0", true);
    // common::ensure_successful_run_on_crate("miniz_oxide", "0.8.5", true);
    // common::ensure_successful_run_on_crate("num-conv", "0.1.0", true);
    // common::ensure_successful_run_on_crate("num_enum", "0.7.3", true);
    // common::ensure_successful_run_on_crate("proc-macro2", "1.0.93", false);
    // common::ensure_successful_run_on_crate("radium", "1.1.0", true);
    // common::ensure_successful_run_on_crate("regex-automata", "0.4.9", true);
    // common::ensure_successful_run_on_crate("ring", "0.17.3", true);
    // common::ensure_successful_run_on_crate("serde_with", "3.12.0", true);
    // common::ensure_successful_run_on_crate("tap", "1.0.1", false);

    // common::ensure_successful_run_on_crate(
    //     "serde_json",
    //     "1.0.140",
    //     Some("2025-03-13"),
    //     common::RunOnCrateOptions::RunPCG {
    //         target: common::Target::Release,
    //         validity_checks: true,
    //     },
    // );

    // We should test this consistently because it's a good loop test
    // common::ensure_successful_run_on_crate(
    //     "tinytemplate",
    //     "1.2.1",
    //     Some("2025-03-13"),
    //     common::RunOnCrateOptions::RunPCG {
    //         target: common::Target::Release,
    //         validity_checks: false,
    //     },
    // );

    // common::ensure_successful_run_on_crate(
    //     "regex-syntax",
    //     "0.8.5",
    //     Some("2025-03-13"),
    //     common::RunOnCrateOptions::RunPCG {
    //         target: common::Target::Debug,
    //         validity_checks: true,
    //     },
    // );

    // common::ensure_successful_run_on_crate(
    //     "crossbeam-deque",
    //     "0.8.6",
    //     None,
    //     common::RunOnCrateOptions::RunPCG {
    //         target: common::Target::Release,
    //         validity_checks: false,
    //     },
    // );

    // common::ensure_successful_run_on_crate(
    //     "itertools",
    //     "0.14.0",
    //     None,
    //     common::RunOnCrateOptions::RunPCG {
    //         target: common::Target::Release,
    //         validity_checks: false,
    //     },
    // );

    // common::ensure_successful_run_on_crate(
    //     "opentelemetry",
    //     "0.28.0",
    //     None,
    //     common::RunOnCrateOptions::RunPCG {
    //         target: common::Target::Release,
    //         validity_checks: false,
    //     },
    // );

    // common::ensure_successful_run_on_crate(
    //     "syn",
    //     "2.0.100",
    //     Some("2025-03-13"),
    //     common::RunOnCrateOptions::RunPCG {
    //         target: common::Target::Release,
    //         validity_checks: true,
    //     },
    // );

    // common::ensure_successful_run_on_crate(
    //     "cfg-if",
    //     "1.0.0",
    //     Some("2025-03-13"),
    //     common::RunOnCrateOptions::RunPCG {
    //         target: common::Target::Release,
    //         validity_checks: false,
    //     },
    // );

    // common::ensure_successful_run_on_crate("toml_edit", "0.22.23", false);
    // common::ensure_successful_run_on_crate("tonic", "0.12.3", true);
    // common::ensure_successful_run_on_crate("wasm-bindgen-backend", "0.2.100", true);
    // common::ensure_successful_run_on_crate("zerovec-derive", "0.10.3", Some("2025-03-13"), true, false);
    // common::ensure_successful_run_on_crate("zerocopy-derive", "0.8.23", Some("2025-03-13"), common::RunOnCrateOptions::RunPCG {
    //     target: common::Target::Debug,
    //     validity_checks: false,
    // });
}
