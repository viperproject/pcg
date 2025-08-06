mod common;

#[allow(unused)]
fn pcg_max_nodes(n: usize) -> Vec<(String, String)> {
    vec![("PCG_MAX_NODES".to_string(), n.to_string())]
}

#[allow(unused)]
#[test]
fn test_selected_crates() {
    // Create tmp directory if it doesn't exist
    std::fs::create_dir_all("tmp").unwrap();

    let warn_only_vars = vec![(
        "PCG_VALIDITY_CHECKS_WARN_ONLY".to_string(),
        "true".to_string(),
    )];

    let visualization_env_vars = vec![
        (
            "PCG_VISUALIZATION_DATA_DIR".to_string(),
            "../../visualization/data".to_string(),
        ),
        ("PCG_VISUALIZATION".to_string(), "true".to_string()),
    ];

    // 58 basic blocks, <= 60 nodes
    common::ensure_successful_run_on_crate(
        "walkdir",
        "2.5.0",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("IntoIter::check_loop"),
            extra_env_vars: vec![],
        },
    );

    // 62 basic blocks, <= 60 nodes
    common::ensure_successful_run_on_crate(
        "petgraph",
        "0.7.1",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("<data::FilterElements<I, F> as std::iter::Iterator>::next"),
            extra_env_vars: vec![],
        },
    );

    // 64 basic blocks, <= 60 nodes
    common::ensure_successful_run_on_crate(
        "strum_macros",
        "0.27.1",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("helpers::case_style::snakify"),
            extra_env_vars: vec![]
        },
    );

    // 51 basic blocks, <= 60 nodes
    common::ensure_successful_run_on_crate(
        "brotli-decompressor",
        "4.0.2",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("copy_from_to"),
            extra_env_vars: vec![],
        },
    );

    // 92 basic blocks, <= 60 nodes
    common::ensure_successful_run_on_crate(
        "aho-corasick",
        "1.1.3",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("nfa::contiguous::Builder::build_from_noncontiguous"),
            extra_env_vars: vec![],
        },
    );

    // 56 basic blocks, <= 60 nodes
    common::ensure_successful_run_on_crate(
        "rustls",
        "0.23.23",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("msgs::handshake::ServerNamePayload::read_hostname"),
            extra_env_vars: vec![],
        },
    );

    // 51 basic blocks, <= 60 nodes
    common::ensure_successful_run_on_crate(
        "slab",
        "0.4.9",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("Slab::<T>::compact"),
            extra_env_vars: vec![],
        },
    );

    // 21 basic blocks, <= 30 nodes
    common::ensure_successful_run_on_crate(
        "form_urlencoded",
        "1.2.1",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("decode"),
            extra_env_vars: vec![],
        },
    );

    // <= 15 basic blocks, <= 30 nodes
    common::ensure_successful_run_on_crate(
        "hashbrown",
        "0.15.2",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("map::VacantEntry::<'a, K, V, S, A>::insert"),
            extra_env_vars: vec![],
        },
    );

    // 12 basic blocks, <= 30 nodes
    common::ensure_successful_run_on_crate(
        "regex-automata",
        "0.4.9",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("hybrid::dfa::Lazy::<'i, 'c>::set_all_transitions"),
            extra_env_vars: vec![],
        },
    );

    // <= 10 basic blocks, <= 20 nodes
    common::ensure_successful_run_on_crate(
        "hashbrown",
        "0.15.2",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("raw_entry::RawOccupiedEntryMut::<'a, K, V, S, A>::replace_entry_with"),
            extra_env_vars: vec![],
        },
    );

    // 18 basic blocks, <= 20 nodes
    common::ensure_successful_run_on_crate(
        "hashbrown",
        "0.15.2",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("map::OccupiedEntry::<'a, K, V, S, A>::replace_entry_with"),
            extra_env_vars: vec![],
        },
    );

    // <= 8 basic blocks, <= 30 nodes
    common::ensure_successful_run_on_crate(
        "gimli",
        "0.31.1",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("read::cfi::UnwindTable::<'a, 'ctx, R, S>::into_current_row"),
            extra_env_vars: vec![],
        },
    );

    // 22 basic blocks, <= 30 nodes
    common::ensure_successful_run_on_crate(
        "log",
        "0.4.26",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("set_logger_inner"),
            extra_env_vars: vec![],
        },
    );

    // <= 20 basic blocks, cycles, <= 20 nodes
    common::ensure_successful_run_on_crate(
        "rustls-native-certs",
        "0.8.1",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("load_native_certs"),
            extra_env_vars: vec![],
        },
    );

    // <= 15 basic blocks, cycles, <= 20 nodes
    common::ensure_successful_run_on_crate(
        "rustix",
        "1.0.2",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("io::errno::retry_on_intr"),
            extra_env_vars: vec![],
        },
    );

    // 23 basic blocks
    common::ensure_successful_run_on_crate(
        "cookie",
        "0.18.1",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("prefix::Prefix::prefix"),
            extra_env_vars: vec![],
        },
    );

    // 22 basic blocks, <= 30 nodes
    common::ensure_successful_run_on_crate(
        "indexmap",
        "2.8.0",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("map::core::RefMut::<'a, K, V>::swap_indices"),
            extra_env_vars: vec![],
        },
    );

    // <= 15 basic blocks, <= 15 nodes
    common::ensure_successful_run_on_crate(
        "memchr",
        "2.7.4",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("memmem::FindIter::<'h, 'n>::into_owned"),
            extra_env_vars: vec![],
        },
    );

    common::ensure_successful_run_on_crate(
        "ahash",
        "0.8.11",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("random_state::RandomState::with_seed"),
            extra_env_vars: vec![],
        },
    );

    // 3 basic blocks
    common::ensure_successful_run_on_crate(
        "tracing-subscriber",
        "0.3.19",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("registry::SpanRef::<'a, R>::with_filter"),
            extra_env_vars: vec![],
        },
    );

    // 7 basic blocks
    common::ensure_successful_run_on_crate(
        "tracing-subscriber",
        "0.3.19",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some(
                "<fmt::format::pretty::Pretty as fmt::format::FormatFields<'writer>>::format_fields",
            ),
            extra_env_vars: vec![],
        },
    );

    // <= 15 basic blocks, <= 15 nodes
    common::ensure_successful_run_on_crate(
        "ring",
        "0.17.14",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some(
                "bssl::<impl core::convert::From<bssl::Result> for core::result::Result<(), error::unspecified::Unspecified>>::from",
            ),
            extra_env_vars: vec![],
        },
    );

    // 14 basic blocks, <= 15 nodes
    common::ensure_successful_run_on_crate(
        "rayon",
        "1.10.0",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some(
                "<iter::chunks::ChunkProducer<P, F> as iter::plumbing::Producer>::into_iter",
            ),
            extra_env_vars: vec![],
        },
    );

    // 30 basic blocks
    common::ensure_successful_run_on_crate(
        "cookie",
        "0.18.1",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("prefix::Prefix::clip"),
            extra_env_vars: vec![],
        },
    );

    // 12 basic blocks <= 15 nodes
    common::ensure_successful_run_on_crate(
        "regex-automata",
        "0.4.9",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("<util::search::PatternSetIter<'a> as core::iter::Iterator>::next"),
            extra_env_vars: vec![],
        },
    );

    // 15 basic blocks <= 20 nodes
    common::ensure_successful_run_on_crate(
        "hashbrown",
        "0.15.2",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("<set::Intersection<'a, T, S, A> as core::iter::Iterator>::next"),
            extra_env_vars: vec![],
        },
    );

    common::ensure_successful_run_on_crate(
        "zip",
        "2.2.3",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("read::ZipFile::<'a>::take_raw_reader"),
            extra_env_vars: vec![],
        },
    );

    // 159 basic blocks
    common::ensure_successful_run_on_crate(
        "serde_yaml",
        "0.9.34+deprecated",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("loader::Loader::<'input>::next_document"),
            extra_env_vars: vec![],
        },
    );

    // 20 basic blocks
    common::ensure_successful_run_on_crate(
        "http",
        "1.3.1",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some(
                "<header::map::ValueIter<'a, T> as std::iter::DoubleEndedIterator>::next_back",
            ),
            extra_env_vars: vec![],
        },
    );

    // 4 basic blocks
    common::ensure_successful_run_on_crate(
        "rustls-pki-types",
        "1.11.0",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("server_name::parser::Parser::<'a>::read_char"),
            extra_env_vars: vec![],
        },
    );

    // 23 basic blocks
    common::ensure_successful_run_on_crate(
        "prost-build",
        "0.13.5",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("code_generator::CodeGenerator::<'_, 'b>::append_type_attributes"),
            extra_env_vars: vec![],
        },
    );

    // cycles, <= 20 basic blocks, <= 30 nodes
    common::ensure_successful_run_on_crate(
        "object",
        "0.36.7",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some(
                "<read::coff::comdat::CoffComdatIterator<'data, 'file, R, Coff> as core::iter::Iterator>::next",
            ),
            extra_env_vars: vec![],
        },
    );

    // <= 20 basic blocks, cycles, <= 20 nodes
    common::ensure_successful_run_on_crate(
        "sha2",
        "0.10.8",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: None,
            extra_env_vars: vec![],
        },
    );

    // 4 basic blocks, cycles, <= 12 nodes
    common::ensure_successful_run_on_crate(
        "rustix",
        "1.0.2",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("buffer::<impl buffer::private::Sealed<T> for &mut [T]>::parts_mut"),
            extra_env_vars: vec![],
        },
    );

    // <10 basic blocks, cycles
    common::ensure_successful_run_on_crate(
        "serde_json",
        "1.0.140",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("<ser::PrettyFormatter<'a> as ser::Formatter>::begin_array"),
            extra_env_vars: vec![],
        },
    );

    // 36 basic blocks
    common::ensure_successful_run_on_crate(
        "flume",
        "0.11.1",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some(
                "<select::Selector<'a, T>::send::SendSelection<'a, T, F, U> as select::Selection<'a, T>>::init",
            ),
            extra_env_vars: vec![],
        },
    );

    // cycles, <= 30 basic blocks, <= 30 nodes
    common::ensure_successful_run_on_crate(
        "hashbrown",
        "0.15.2",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("raw::RawTable::<T, A>::get_many_mut"),
            extra_env_vars: vec![],
        },
    );

    // cycles, <= 10 basic blocks, <= 10 nodes
    common::ensure_successful_run_on_crate(
        "hyper-tls",
        "0.6.0",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("client::err"),
            extra_env_vars: vec![],
        },
    );

    // 17 basic blocks, <= 30 nodes
    common::ensure_successful_run_on_crate(
        "httparse",
        "1.10.1",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("simd::swar::match_header_name_vectored"),
            extra_env_vars: vec![],
        },
    );

    // Cycle, 10 blocks, <= 10 nodes
    common::ensure_successful_run_on_crate(
        "tracing-subscriber",
        "0.3.19",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("registry::SpanRef::<'a, R>::try_with_filter"),
            extra_env_vars: vec![],
        },
    );

    // 45 blocks
    // common::ensure_successful_run_on_crate("ring",
    //     "0.17.14",
    //     Some("2025-03-13"),
    //     common::RunOnCrateOptions::RunPCG {
    //         target: common::Target::Debug,
    //         validity_checks: true,
    //         function: Some("ec::suite_b::ops::p384::p384_scalar_inv_to_mont"),
    //         extra_env_vars: vec![],
    //     },
    // );

    // 7 basic blocks, <= 20 nodes
    common::ensure_successful_run_on_crate(
        "combine",
        "4.6.7",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("<&'a str as stream::RangeStreamOnce>::uncons_while"),
            extra_env_vars: vec![],
        },
    );

    // 8 basic blocks, <= 20 nodes
    common::ensure_successful_run_on_crate(
        "encoding_rs",
        "0.8.35",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("handles::ByteSource::<'a>::check_available"),
            extra_env_vars: vec![],
        },
    );

    // 132 basic blocks, <= 20 nodes
    common::ensure_successful_run_on_crate(
        "glob",
        "0.3.2",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("glob_with"),
            extra_env_vars: vec![],
        },
    );

    // 140 basic blocks
    common::ensure_successful_run_on_crate(
        "clap_builder",
        "4.5.32",
        None,
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: false,
            function: Some("output::help_template::HelpTemplate::<'_, '_>::write_all_args"),
            extra_env_vars: vec![],
        },
    );

    // 11 basic blocks, <= 20 nodes
    common::ensure_successful_run_on_crate(
        "indexmap",
        "2.8.0",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("map::core::RefMut::<'a, K, V>::shift_remove_finish"),
            extra_env_vars: vec![],
        },
    );

    // 3 basic blocks
    common::ensure_successful_run_on_crate(
        "hyper",
        "1.6.0",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("rt::io::ReadBufCursor::<'_>::as_mut"),
            extra_env_vars: vec![],
        },
    );

    // 4 basic blocks
    common::ensure_successful_run_on_crate(
        "regex-automata",
        "0.4.9",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("util::search::Input::<'h>::set_start"),
            extra_env_vars: vec![],
        },
    );

    // 7 basic blocks
    common::ensure_successful_run_on_crate(
        "bitvec",
        "1.0.1",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("<domain::Domain<'a, wyz::Const, T, O> as std::fmt::Binary>::fmt"),
            extra_env_vars: vec![],
        },
    );

    // 9 basic blocks, <= 20 nodes
    common::ensure_successful_run_on_crate(
        "regex-automata",
        "0.4.9",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("util::iter::Searcher::<'h>::handle_overlapping_empty_half_match"),
            extra_env_vars: vec![],
        },
    );

    // 3 basic blocks
    common::ensure_successful_run_on_crate(
        "tracing-subscriber",
        "0.3.19",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some(
                "<fmt::format::DefaultFields as field::MakeVisitor<fmt::format::Writer<'a>>>::make_visitor",
            ),
            extra_env_vars: vec![],
        },
    );

    // 4 basic blocks
    common::ensure_successful_run_on_crate(
        "tracing-subscriber",
        "0.3.19",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("fmt::fmt_layer::FormattedFields::<E>::as_writer"),
            extra_env_vars: vec![],
        },
    );

    // 7 basic blocks
    common::ensure_successful_run_on_crate(
        "tracing-subscriber",
        "0.3.19",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("<filter::targets::Targets as std::str::FromStr>::from_str"),
            extra_env_vars: vec![],
        },
    );

    // 11 basic blocks
    common::ensure_successful_run_on_crate(
        "serde_yaml",
        "0.9.34+deprecated",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some(
                "<de::MapAccess<'de, 'document, 'map> as serde::de::MapAccess<'de>>::next_value_seed",
            ),
            extra_env_vars: vec![],
        },
    );

    // 32 basic blocks
    common::ensure_successful_run_on_crate(
        "serde_yaml",
        "0.9.34+deprecated",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some(
                "<de::SeqAccess<'de, 'document, 'seq> as serde::de::SeqAccess<'de>>::next_element_seed",
            ),
            extra_env_vars: vec![],
        },
    );

    // 8 basic blocks
    common::ensure_successful_run_on_crate(
        "tokio-io-timeout",
        "1.2.0",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("TimeoutState::reset"),
            extra_env_vars: vec![],
        },
    );

    common::ensure_successful_run_on_crate(
        "tokio-io-timeout",
        "1.2.0",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("TimeoutState::poll_check"),
            extra_env_vars: vec![],
        },
    );

    // 4 basic blocks
    common::ensure_successful_run_on_crate(
        "miniz_oxide",
        "0.8.5",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("inflate::output_buffer::OutputBuffer::<'a>::write_byte"),
            extra_env_vars: vec![],
        },
    );

    // 7 basic blocks
    common::ensure_successful_run_on_crate(
        "serde_json",
        "1.0.140",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("<read::SliceRead<'a> as read::Read<'a>>::peek"),
            extra_env_vars: vec![],
        },
    );

    // 8 basic blocks
    common::ensure_successful_run_on_crate(
        "serde_json",
        "1.0.140",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("<read::SliceRead<'a> as read::Read<'a>>::next"),
            extra_env_vars: vec![],
        },
    );

    // 13 basic blocks
    common::ensure_successful_run_on_crate(
        "serde_json",
        "1.0.140",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("read::SliceRead::<'a>::skip_to_escape_slow"),
            extra_env_vars: vec![],
        },
    );

    // 23 basic blocks
    common::ensure_successful_run_on_crate(
        "tokio-io-timeout",
        "1.2.0",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("TimeoutState::poll_check"),
            extra_env_vars: vec![],
        },
    );

    // 27 basic blocks
    common::ensure_successful_run_on_crate(
        "bstr",
        "1.11.3",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("<ext_slice::FieldsWith<'a, F> as core::iter::Iterator>::next"),
            extra_env_vars: vec![],
        },
    );

    // 29 basic blocks
    common::ensure_successful_run_on_crate(
        "serde_yaml",
        "0.9.34+deprecated",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("value::debug::<impl std::fmt::Debug for mapping::Mapping>::fmt"),
            extra_env_vars: vec![],
        },
    );

    // 198 basic blocks
    common::ensure_successful_run_on_crate(
        "brotli",
        "7.0.0",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("enc::static_dict::ComplexFindMatchLengthWithLimit"),
            extra_env_vars: vec![],
        },
    );

    common::ensure_successful_run_on_crate(
        "winnow",
        "0.7.4",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some(
                "<stream::token::TokenSlice<'_, T> as stream::UpdateSlice>::update_slice",
            ),
            extra_env_vars: vec![],
        },
    );

    common::ensure_successful_run_on_crate(
        "matchit",
        "0.8.6",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("tree::Node::<T>::at"),
            extra_env_vars: vec![],
        },
    );

    common::ensure_successful_run_on_crate(
        "regex-automata",
        "0.4.9",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: Some("dfa::dense::DFA::<&'a [u32]>::from_bytes"),
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
            function: Some("parser_state::ParserState::<'i, R>::stack_match_pop"),
            extra_env_vars: vec![],
        },
    );

    common::ensure_successful_run_on_crate(
        "crypto-bigint",
        "0.6.1",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: false,
            function: None,
            extra_env_vars: vec![("PCG_MAX_BASIC_BLOCKS".to_string(), "13".to_string())],
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

    common::ensure_successful_run_on_crate(
        "tracing-subscriber",
        "0.3.19",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: false,
            function: None,
            extra_env_vars: vec![],
        },
    );

    common::ensure_successful_run_on_crate(
        "rustls",
        "0.23.23",
        Some("2025-03-13"),
        common::RunOnCrateOptions::RunPCG {
            target: common::Target::Debug,
            validity_checks: true,
            function: None,
            extra_env_vars: vec![],
        },
    );
}
