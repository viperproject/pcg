#![feature(let_chains)]
#![allow(dead_code)]
use itertools::Itertools;

mod common;

#[allow(unused)]
fn pcg_max_nodes(n: usize) -> Vec<(String, String)> {
    vec![("PCG_MAX_NODES".to_string(), n.to_string())]
}

#[derive(Debug)]
struct TestCrateFunction {
    function_name: &'static str,
    debug_failure: bool,
    metadata: TestFunctionMetadata,
}

impl TestCrateFunction {
    fn new(function_name: &'static str, debug_failure: bool, num_bbs: Option<usize>) -> Self {
        Self {
            function_name,
            debug_failure,
            metadata: TestFunctionMetadata { num_bbs },
        }
    }
}

#[derive(Debug)]
enum TestCrateType {
    EntireCrate,
    Function(TestCrateFunction),
}

impl TestCrateType {
    fn function(function_name: &'static str, num_bbs: Option<usize>) -> Self {
        Self::Function(TestCrateFunction::new(function_name, false, num_bbs))
    }

    fn function_debug_failure(function_name: &'static str, num_bbs: Option<usize>) -> Self {
        Self::Function(TestCrateFunction::new(function_name, true, num_bbs))
    }
}

#[derive(Debug)]
struct TestFunctionMetadata {
    num_bbs: Option<usize>,
}

#[derive(Debug)]
struct SelectedCrateTestCase {
    crate_name: &'static str,
    crate_version: &'static str,
    crate_download_date: Option<&'static str>,
    test_type: TestCrateType,
}

impl SelectedCrateTestCase {
    fn new(
        crate_name: &'static str,
        crate_version: &'static str,
        crate_download_date: Option<&'static str>,
        test_type: TestCrateType,
    ) -> Self {
        Self {
            crate_name,
            crate_version,
            crate_download_date,
            test_type,
        }
    }

    fn num_bbs(&self) -> Option<usize> {
        match &self.test_type {
            TestCrateType::EntireCrate => None,
            TestCrateType::Function(function) => function.metadata.num_bbs,
        }
    }

    fn function_name(&self) -> Option<&'static str> {
        match &self.test_type {
            TestCrateType::EntireCrate => None,
            TestCrateType::Function(function) => Some(function.function_name),
        }
    }

    fn debug_failure(&self) {
        let visualization_env_vars = vec![
            (
                "PCG_VISUALIZATION_DATA_DIR".to_string(),
                "../../visualization/data".to_string(),
            ),
            (
                "PCG_VALIDITY_CHECKS_WARN_ONLY".to_string(),
                "true".to_string(),
            ),
            ("PCG_VISUALIZATION".to_string(), "true".to_string()),
        ];
        common::ensure_successful_run_on_crate(
            self.crate_name,
            self.crate_version,
            self.crate_download_date,
            common::RunOnCrateOptions::RunPCG {
                target: common::Target::Debug,
                validity_checks: true,
                function: self.function_name(),
                extra_env_vars: visualization_env_vars,
            },
        );
    }

    fn run(&self) {
        if let TestCrateType::Function(function) = &self.test_type
            && function.debug_failure
        {
            self.debug_failure();
            panic!("Stop for failure debugging");
        }
        let result = common::run_on_crate(
            self.crate_name,
            self.crate_version,
            self.crate_download_date,
            common::RunOnCrateOptions::RunPCG {
                target: common::Target::Debug,
                validity_checks: true,
                function: self.function_name(),
                extra_env_vars: vec![],
            },
        );
        if matches!(result, common::RunOnCrateResult::Failed) {
            tracing::error!("Test case failed: {:?}", self);
            if self.function_name().is_some() {
                tracing::info!("Will re-run with visualization");
                self.debug_failure();
                panic!("Test failed (produced debug visualization)");
            } else {
                panic!("Test failed");
            }
        }
    }
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

    let test_cases = vec![
        SelectedCrateTestCase::new(
            "syn",
            "2.0.100",
            Some("2025-03-13"),
            TestCrateType::function("punctuated::Pair::<T, P>::value_mut", Some(6)),
        ),
        SelectedCrateTestCase::new(
            "pyo3-macros-backend",
            "0.24.0",
            Some("2025-03-13"),
            TestCrateType::function("method::FnArg::<'a>::to_varargs_mut", Some(19)),
        ),
        SelectedCrateTestCase::new(
            "flume",
            "0.11.1",
            Some("2025-03-13"),
            TestCrateType::function(
                "<select::Selector<'a, T>::recv::RecvSelection<'a, T, F, U> as select::Selection<'a, T>>::init",
                None,
            ),
        ),
        SelectedCrateTestCase::new(
            "regex-automata",
            "0.4.9",
            Some("2025-03-13"),
            TestCrateType::function(
                "<util::captures::GroupInfoAllNames<'a> as core::iter::Iterator>::next",
                Some(33),
            ),
        ),
        SelectedCrateTestCase::new(
            "axum",
            "0.8.1",
            Some("2025-03-13"),
            TestCrateType::function(
                "<extract::path::de::ValueDeserializer<'de> as serde::Deserializer<'de>>::deserialize_tuple",
                Some(16),
            ),
        ),
        SelectedCrateTestCase::new(
            "object",
            "0.36.7",
            Some("2025-03-13"),
            TestCrateType::function(
                "<read::coff::comdat::CoffComdatIterator<'data, 'file, R, Coff> as core::iter::Iterator>::next",
                Some(20),
            ),
        ),
        SelectedCrateTestCase::new(
            "dashmap",
            "6.1.0",
            Some("2025-03-13"),
            TestCrateType::function("DashMap::<K, V, S>::try_reserve", Some(26)),
        ),
        SelectedCrateTestCase::new(
            "gimli",
            "0.31.1",
            Some("2025-03-13"),
            TestCrateType::function(
                "read::cfi::UnwindTable::<'a, 'ctx, R, S>::into_current_row",
                Some(8),
            ),
        ),
        SelectedCrateTestCase::new(
            "rayon",
            "1.10.0",
            Some("2025-03-13"),
            TestCrateType::function(
                "<str::CharIndicesProducer<'ch> as iter::plumbing::UnindexedProducer>::split",
                Some(10),
            ),
        ),
        SelectedCrateTestCase::new(
            "h2",
            "0.4.8",
            Some("2025-03-13"),
            TestCrateType::function(
                "<error::Error as std::convert::From<proto::error::Error>>::from",
                Some(20),
            ),
        ),
        SelectedCrateTestCase::new(
            "combine",
            "4.6.7",
            Some("2025-03-13"),
            TestCrateType::function(
                "<&'a str as stream::RangeStreamOnce>::uncons_while",
                Some(7),
            ),
        ),
        SelectedCrateTestCase::new(
            "indexmap",
            "2.8.0",
            Some("2025-03-13"),
            TestCrateType::function(
                "map::core::raw_entry_v1::RawEntryBuilder::<'a, K, V, S>::from_key_hashed_nocheck",
                Some(11),
            ),
        ),
        SelectedCrateTestCase::new(
            "serde_json",
            "1.0.140",
            Some("2025-03-13"),
            TestCrateType::function("read::SliceRead::<'a>::parse_str_bytes", Some(55)),
        ),
        SelectedCrateTestCase::new(
            "pyo3",
            "0.24.0",
            Some("2025-03-13"),
            TestCrateType::function(
                "pyclass::create_type_object::GetSetDefBuilder::add_getter",
                Some(6),
            ),
        ),
        SelectedCrateTestCase::new(
            "winnow",
            "0.7.4",
            Some("2025-03-13"),
            TestCrateType::function(
                "<stream::token::TokenSlice<'_, T> as stream::UpdateSlice>::update_slice",
                Some(3),
            ),
        ),
        SelectedCrateTestCase::new(
            "wasm-bindgen-backend",
            "0.2.100",
            Some("2025-03-13"),
            TestCrateType::function(
                "<ast::Export as codegen::TryToTokens>::try_to_tokens::unwrap_nested_types",
                Some(12),
            ),
        ),
        // <= 13 basic blocks, <= 60 nodes
        SelectedCrateTestCase::new(
            "tinytemplate",
            "1.2.1",
            Some("2025-03-13"),
            TestCrateType::function(
                "compiler::TemplateCompiler::<'template>::consume_text",
                Some(13),
            ),
        ),
        // 5 basic blocks, <= 60 nodes
        SelectedCrateTestCase::new(
            "sharded-slab",
            "0.1.7",
            Some("2025-03-13"),
            TestCrateType::function("pool::RefMut::<'a, T, C>::downgrade", Some(5)),
        ),
        // 36 basic blocks, <= 60 nodes
        SelectedCrateTestCase::new(
            "tempfile",
            "3.18.0",
            Some("2025-03-13"),
            TestCrateType::function(
                "<spooled::SpooledTempFile as std::io::Write>::write",
                Some(36),
            ),
        ),
        // 4 basic blocks, <= 60 nodes
        SelectedCrateTestCase::new(
            "miniz_oxide",
            "0.8.5",
            Some("2025-03-13"),
            TestCrateType::function(
                "inflate::output_buffer::InputWrapper::<'a>::read_byte",
                Some(4),
            ),
        ),
        // 4 basic blocks, <= 60 nodes
        SelectedCrateTestCase::new(
            "async-trait",
            "0.1.87",
            Some("2025-03-13"),
            TestCrateType::function(
                "<lifetime::CollectLifetimes as syn::visit_mut::VisitMut>::visit_type_reference_mut",
                Some(4),
            ),
        ),
        SelectedCrateTestCase::new(
            "hashbrown",
            "0.15.2",
            Some("2025-03-13"),
            TestCrateType::function(
                "map::OccupiedEntry::<'a, K, V, S, A>::remove_entry",
                Some(4),
            ),
        ),
        // 18 basic blocks, <= 60 nodes
        SelectedCrateTestCase::new(
            "unicode-segmentation",
            "1.12.0",
            Some("2025-03-13"),
            TestCrateType::function(
                "<sentence::USentenceBounds<'a> as core::iter::Iterator>::next",
                Some(18),
            ),
        ),
        // 58 basic blocks, <= 60 nodes
        SelectedCrateTestCase::new(
            "walkdir",
            "2.5.0",
            Some("2025-03-13"),
            TestCrateType::function("IntoIter::check_loop", Some(58)),
        ),
        // 62 basic blocks, <= 60 nodes
        SelectedCrateTestCase::new(
            "petgraph",
            "0.7.1",
            Some("2025-03-13"),
            TestCrateType::function(
                "<data::FilterElements<I, F> as std::iter::Iterator>::next",
                Some(62),
            ),
        ),
        // 64 basic blocks, <= 60 nodes
        SelectedCrateTestCase::new(
            "strum_macros",
            "0.27.1",
            Some("2025-03-13"),
            TestCrateType::function("helpers::case_style::snakify", Some(64)),
        ),
        // 51 basic blocks, <= 60 nodes
        SelectedCrateTestCase::new(
            "brotli-decompressor",
            "4.0.2",
            Some("2025-03-13"),
            TestCrateType::function("copy_from_to", Some(51)),
        ),
        // 92 basic blocks, <= 60 nodes
        SelectedCrateTestCase::new(
            "aho-corasick",
            "1.1.3",
            Some("2025-03-13"),
            TestCrateType::function(
                "nfa::contiguous::Builder::build_from_noncontiguous",
                Some(92),
            ),
        ),
        // 56 basic blocks, <= 60 nodes
        SelectedCrateTestCase::new(
            "rustls",
            "0.23.23",
            Some("2025-03-13"),
            TestCrateType::function(
                "msgs::handshake::ServerNamePayload::read_hostname",
                Some(56),
            ),
        ),
        // 51 basic blocks, <= 60 nodes
        SelectedCrateTestCase::new(
            "slab",
            "0.4.9",
            Some("2025-03-13"),
            TestCrateType::function("Slab::<T>::compact", Some(51)),
        ),
        // 21 basic blocks, <= 30 nodes
        SelectedCrateTestCase::new(
            "form_urlencoded",
            "1.2.1",
            Some("2025-03-13"),
            TestCrateType::function("decode", Some(21)),
        ),
        // <= 15 basic blocks, <= 30 nodes
        SelectedCrateTestCase::new(
            "hashbrown",
            "0.15.2",
            Some("2025-03-13"),
            TestCrateType::function("map::VacantEntry::<'a, K, V, S, A>::insert", Some(15)),
        ),
        // 12 basic blocks, <= 30 nodes
        SelectedCrateTestCase::new(
            "regex-automata",
            "0.4.9",
            Some("2025-03-13"),
            TestCrateType::function("hybrid::dfa::Lazy::<'i, 'c>::set_all_transitions", Some(12)),
        ),
        // <= 10 basic blocks, <= 20 nodes
        SelectedCrateTestCase::new(
            "hashbrown",
            "0.15.2",
            Some("2025-03-13"),
            TestCrateType::function(
                "raw_entry::RawOccupiedEntryMut::<'a, K, V, S, A>::replace_entry_with",
                Some(10),
            ),
        ),
        // 18 basic blocks, <= 20 nodes
        SelectedCrateTestCase::new(
            "hashbrown",
            "0.15.2",
            Some("2025-03-13"),
            TestCrateType::function(
                "map::OccupiedEntry::<'a, K, V, S, A>::replace_entry_with",
                Some(18),
            ),
        ),
        // 22 basic blocks, <= 30 nodes
        SelectedCrateTestCase::new(
            "log",
            "0.4.26",
            Some("2025-03-13"),
            TestCrateType::function("set_logger_inner", Some(22)),
        ),
        // <= 20 basic blocks, cycles, <= 20 nodes
        SelectedCrateTestCase::new(
            "rustls-native-certs",
            "0.8.1",
            Some("2025-03-13"),
            TestCrateType::function("load_native_certs", Some(20)),
        ),
        // <= 15 basic blocks, cycles, <= 20 nodes
        SelectedCrateTestCase::new(
            "rustix",
            "1.0.2",
            Some("2025-03-13"),
            TestCrateType::function("io::errno::retry_on_intr", Some(15)),
        ),
        // 23 basic blocks
        SelectedCrateTestCase::new(
            "cookie",
            "0.18.1",
            Some("2025-03-13"),
            TestCrateType::function("prefix::Prefix::prefix", Some(23)),
        ),
        // 22 basic blocks, <= 30 nodes
        SelectedCrateTestCase::new(
            "indexmap",
            "2.8.0",
            Some("2025-03-13"),
            TestCrateType::function("map::core::RefMut::<'a, K, V>::swap_indices", Some(22)),
        ),
        // <= 15 basic blocks, <= 15 nodes
        SelectedCrateTestCase::new(
            "memchr",
            "2.7.4",
            Some("2025-03-13"),
            TestCrateType::function("memmem::FindIter::<'h, 'n>::into_owned", Some(15)),
        ),
        SelectedCrateTestCase::new(
            "ahash",
            "0.8.11",
            Some("2025-03-13"),
            TestCrateType::function("random_state::RandomState::with_seed", None),
        ),
        // 3 basic blocks
        SelectedCrateTestCase::new(
            "tracing-subscriber",
            "0.3.19",
            Some("2025-03-13"),
            TestCrateType::function("registry::SpanRef::<'a, R>::with_filter", Some(3)),
        ),
        // 7 basic blocks
        SelectedCrateTestCase::new(
            "tracing-subscriber",
            "0.3.19",
            Some("2025-03-13"),
            TestCrateType::EntireCrate,
        ),
        // <= 15 basic blocks, <= 15 nodes
        SelectedCrateTestCase::new(
            "ring",
            "0.17.14",
            Some("2025-03-13"),
            TestCrateType::EntireCrate,
        ),
        // 14 basic blocks, <= 15 nodes
        SelectedCrateTestCase::new(
            "rayon",
            "1.10.0",
            Some("2025-03-13"),
            TestCrateType::EntireCrate,
        ),
        // 30 basic blocks
        SelectedCrateTestCase::new(
            "cookie",
            "0.18.1",
            Some("2025-03-13"),
            TestCrateType::function("prefix::Prefix::clip", Some(30)),
        ),
        // 12 basic blocks <= 15 nodes
        SelectedCrateTestCase::new(
            "regex-automata",
            "0.4.9",
            Some("2025-03-13"),
            TestCrateType::function(
                "<util::search::PatternSetIter<'a> as core::iter::Iterator>::next",
                Some(12),
            ),
        ),
        // 15 basic blocks <= 20 nodes
        SelectedCrateTestCase::new(
            "hashbrown",
            "0.15.2",
            Some("2025-03-13"),
            TestCrateType::function(
                "<set::Intersection<'a, T, S, A> as core::iter::Iterator>::next",
                Some(15),
            ),
        ),
        SelectedCrateTestCase::new(
            "zip",
            "2.2.3",
            Some("2025-03-13"),
            TestCrateType::function("read::ZipFile::<'a>::take_raw_reader", None),
        ),
        // 159 basic blocks
        SelectedCrateTestCase::new(
            "serde_yaml",
            "0.9.34+deprecated",
            Some("2025-03-13"),
            TestCrateType::function("loader::Loader::<'input>::next_document", Some(159)),
        ),
        // 20 basic blocks
        SelectedCrateTestCase::new(
            "http",
            "1.3.1",
            Some("2025-03-13"),
            TestCrateType::EntireCrate,
        ),
        // 4 basic blocks
        SelectedCrateTestCase::new(
            "rustls-pki-types",
            "1.11.0",
            Some("2025-03-13"),
            TestCrateType::function("server_name::parser::Parser::<'a>::read_char", Some(4)),
        ),
        // 23 basic blocks
        SelectedCrateTestCase::new(
            "prost-build",
            "0.13.5",
            Some("2025-03-13"),
            TestCrateType::function(
                "code_generator::CodeGenerator::<'_, 'b>::append_type_attributes",
                Some(23),
            ),
        ),
        // cycles, <= 20 basic blocks, <= 30 nodes
        SelectedCrateTestCase::new(
            "object",
            "0.36.7",
            Some("2025-03-13"),
            TestCrateType::EntireCrate,
        ),
        // <= 20 basic blocks, cycles, <= 20 nodes
        SelectedCrateTestCase::new("sha2", "0.10.8", None, TestCrateType::EntireCrate),
        // 4 basic blocks, cycles, <= 12 nodes
        SelectedCrateTestCase::new(
            "rustix",
            "1.0.2",
            Some("2025-03-13"),
            TestCrateType::function(
                "buffer::<impl buffer::private::Sealed<T> for &mut [T]>::parts_mut",
                Some(4),
            ),
        ),
        // <10 basic blocks, cycles
        SelectedCrateTestCase::new(
            "serde_json",
            "1.0.140",
            Some("2025-03-13"),
            TestCrateType::function(
                "<ser::PrettyFormatter<'a> as ser::Formatter>::begin_array",
                None,
            ),
        ),
        SelectedCrateTestCase::new(
            "flume",
            "0.11.1",
            Some("2025-03-13"),
            TestCrateType::EntireCrate,
        ),
        // cycles, <= 30 basic blocks, <= 30 nodes
        SelectedCrateTestCase::new(
            "hashbrown",
            "0.15.2",
            Some("2025-03-13"),
            TestCrateType::function("raw::RawTable::<T, A>::get_many_mut", Some(30)),
        ),
        // cycles, <= 10 basic blocks, <= 10 nodes
        SelectedCrateTestCase::new(
            "hyper-tls",
            "0.6.0",
            Some("2025-03-13"),
            TestCrateType::function("client::err", Some(10)),
        ),
        // 17 basic blocks, <= 30 nodes
        SelectedCrateTestCase::new(
            "httparse",
            "1.10.1",
            Some("2025-03-13"),
            TestCrateType::function("simd::swar::match_header_name_vectored", Some(17)),
        ),
        // Cycle, 10 blocks, <= 10 nodes
        SelectedCrateTestCase::new(
            "tracing-subscriber",
            "0.3.19",
            Some("2025-03-13"),
            TestCrateType::function("registry::SpanRef::<'a, R>::try_with_filter", None),
        ),
        // common::ensure_successful_run_on_crate("ring",
        SelectedCrateTestCase::new(
            "ring",
            "0.17.14",
            Some("2025-03-13"),
            TestCrateType::function("ec::suite_b::ops::p384::p384_scalar_inv_to_mont", None),
        ),
        // 8 basic blocks, <= 20 nodes
        SelectedCrateTestCase::new(
            "encoding_rs",
            "0.8.35",
            Some("2025-03-13"),
            TestCrateType::function("handles::ByteSource::<'a>::check_available", Some(8)),
        ),
        // 132 basic blocks, <= 20 nodes
        SelectedCrateTestCase::new(
            "glob",
            "0.3.2",
            Some("2025-03-13"),
            TestCrateType::function("glob_with", Some(132)),
        ),
        // 140 basic blocks
        SelectedCrateTestCase::new(
            "clap_builder",
            "4.5.32",
            None,
            TestCrateType::function(
                "output::help_template::HelpTemplate::<'_, '_>::write_all_args",
                Some(140),
            ),
        ), // Note: original had validity_checks: false
        // 11 basic blocks, <= 20 nodes
        SelectedCrateTestCase::new(
            "indexmap",
            "2.8.0",
            Some("2025-03-13"),
            TestCrateType::function(
                "map::core::RefMut::<'a, K, V>::shift_remove_finish",
                Some(11),
            ),
        ),
        // 3 basic blocks
        SelectedCrateTestCase::new(
            "hyper",
            "1.6.0",
            Some("2025-03-13"),
            TestCrateType::function("rt::io::ReadBufCursor::<'_>::as_mut", Some(3)),
        ),
        // 4 basic blocks
        SelectedCrateTestCase::new(
            "regex-automata",
            "0.4.9",
            Some("2025-03-13"),
            TestCrateType::function("util::search::Input::<'h>::set_start", Some(4)),
        ),
        // 7 basic blocks
        SelectedCrateTestCase::new(
            "bitvec",
            "1.0.1",
            Some("2025-03-13"),
            TestCrateType::function(
                "<domain::Domain<'a, wyz::Const, T, O> as std::fmt::Binary>::fmt",
                Some(7),
            ),
        ),
        // 9 basic blocks, <= 20 nodes
        SelectedCrateTestCase::new(
            "regex-automata",
            "0.4.9",
            Some("2025-03-13"),
            TestCrateType::function(
                "util::iter::Searcher::<'h>::handle_overlapping_empty_half_match",
                Some(9),
            ),
        ),
        // 3 basic blocks
        SelectedCrateTestCase::new(
            "tracing-subscriber",
            "0.3.19",
            Some("2025-03-13"),
            TestCrateType::EntireCrate,
        ),
        // 4 basic blocks
        SelectedCrateTestCase::new(
            "tracing-subscriber",
            "0.3.19",
            Some("2025-03-13"),
            TestCrateType::function("fmt::fmt_layer::FormattedFields::<E>::as_writer", Some(4)),
        ),
        // 7 basic blocks
        SelectedCrateTestCase::new(
            "tracing-subscriber",
            "0.3.19",
            Some("2025-03-13"),
            TestCrateType::function(
                "<filter::targets::Targets as std::str::FromStr>::from_str",
                Some(7),
            ),
        ),
        // 11 basic blocks
        SelectedCrateTestCase::new(
            "serde_yaml",
            "0.9.34+deprecated",
            Some("2025-03-13"),
            TestCrateType::EntireCrate,
        ),
        // 32 basic blocks
        SelectedCrateTestCase::new(
            "serde_yaml",
            "0.9.34+deprecated",
            Some("2025-03-13"),
            TestCrateType::EntireCrate,
        ),
        // 8 basic blocks
        SelectedCrateTestCase::new(
            "tokio-io-timeout",
            "1.2.0",
            Some("2025-03-13"),
            TestCrateType::function("TimeoutState::reset", Some(8)),
        ),
        SelectedCrateTestCase::new(
            "tokio-io-timeout",
            "1.2.0",
            Some("2025-03-13"),
            TestCrateType::function("TimeoutState::poll_check", None),
        ),
        // 4 basic blocks
        SelectedCrateTestCase::new(
            "miniz_oxide",
            "0.8.5",
            Some("2025-03-13"),
            TestCrateType::function(
                "inflate::output_buffer::OutputBuffer::<'a>::write_byte",
                Some(4),
            ),
        ),
        // 7 basic blocks
        SelectedCrateTestCase::new(
            "serde_json",
            "1.0.140",
            Some("2025-03-13"),
            TestCrateType::function("<read::SliceRead<'a> as read::Read<'a>>::peek", Some(7)),
        ),
        // 8 basic blocks
        SelectedCrateTestCase::new(
            "serde_json",
            "1.0.140",
            Some("2025-03-13"),
            TestCrateType::function("<read::SliceRead<'a> as read::Read<'a>>::next", Some(8)),
        ),
        // 13 basic blocks
        SelectedCrateTestCase::new(
            "serde_json",
            "1.0.140",
            Some("2025-03-13"),
            TestCrateType::function("read::SliceRead::<'a>::skip_to_escape_slow", Some(13)),
        ),
        // 23 basic blocks
        SelectedCrateTestCase::new(
            "tokio-io-timeout",
            "1.2.0",
            Some("2025-03-13"),
            TestCrateType::function("TimeoutState::poll_check", Some(23)),
        ),
        // 27 basic blocks
        SelectedCrateTestCase::new(
            "bstr",
            "1.11.3",
            Some("2025-03-13"),
            TestCrateType::function(
                "<ext_slice::FieldsWith<'a, F> as core::iter::Iterator>::next",
                Some(27),
            ),
        ),
        // 29 basic blocks
        SelectedCrateTestCase::new(
            "serde_yaml",
            "0.9.34+deprecated",
            Some("2025-03-13"),
            TestCrateType::function(
                "value::debug::<impl std::fmt::Debug for mapping::Mapping>::fmt",
                Some(29),
            ),
        ),
        // 198 basic blocks
        SelectedCrateTestCase::new(
            "brotli",
            "7.0.0",
            Some("2025-03-13"),
            TestCrateType::function(
                "enc::static_dict::ComplexFindMatchLengthWithLimit",
                Some(198),
            ),
        ),
        SelectedCrateTestCase::new(
            "matchit",
            "0.8.6",
            Some("2025-03-13"),
            TestCrateType::function("tree::Node::<T>::at", None),
        ),
        SelectedCrateTestCase::new(
            "regex-automata",
            "0.4.9",
            Some("2025-03-13"),
            TestCrateType::function("dfa::dense::DFA::<&'a [u32]>::from_bytes", None),
        ),
        SelectedCrateTestCase::new(
            "pest",
            "2.7.15",
            Some("2025-03-13"),
            TestCrateType::function("parser_state::ParserState::<'i, R>::stack_match_pop", None),
        ),
        SelectedCrateTestCase::new("crypto-bigint", "0.6.1", None, TestCrateType::EntireCrate), // Note: original had extra_env_vars and validity_checks: false
        SelectedCrateTestCase::new("idna", "1.0.3", None, TestCrateType::EntireCrate), // Note: original had validity_checks: false
        SelectedCrateTestCase::new(
            "chrono",
            "0.4.40",
            Some("2025-03-13"),
            TestCrateType::function("format::scan::timezone_offset_2822", None),
        ), // Note: original had validity_checks: false
        // for determining if a lifetime projection is live at a point.
        SelectedCrateTestCase::new(
            "yaml-rust",
            "0.4.5",
            Some("2025-03-13"),
            TestCrateType::function("parser::Parser::<T>::stream_start", None),
        ),
        SelectedCrateTestCase::new(
            "flate2",
            "1.1.0",
            Some("2025-03-13"),
            TestCrateType::function(
                "<gz::write::MultiGzDecoder<W> as std::io::Write>::write",
                None,
            ),
        ),
        SelectedCrateTestCase::new(
            "pest",
            "2.7.15",
            Some("2025-03-13"),
            TestCrateType::function("parser_state::ParserState::<'i, R>::match_char_by", None),
        ),
        SelectedCrateTestCase::new(
            "linked-hash-map",
            "0.5.6",
            Some("2025-03-13"),
            TestCrateType::function("LinkedHashMap::<K, V, S>::get_refresh", None),
        ),
        SelectedCrateTestCase::new(
            "serde_yaml",
            "0.9.34+deprecated",
            Some("2025-03-13"),
            TestCrateType::function("libyaml::emitter::Emitter::<'a>::flush", None),
        ),
        // common::ensure_successful_run_on_crate(
        SelectedCrateTestCase::new(
            "brotli-decompressor",
            "4.0.2",
            Some("2025-03-13"),
            TestCrateType::function("<MemPool<'a, T> as core::default::Default>::default", None),
        ),
        SelectedCrateTestCase::new(
            "predicates-tree",
            "1.0.12",
            None,
            TestCrateType::EntireCrate,
        ),
        SelectedCrateTestCase::new(
            "concurrent-queue",
            "2.5.0",
            None,
            TestCrateType::EntireCrate,
        ),
        SelectedCrateTestCase::new(
            "encoding_rs",
            "0.8.35",
            Some("2025-03-13"),
            TestCrateType::function("shift_jis::ShiftJisEncoder::encode_from_utf16_raw", None),
        ), // Note: original had validity_checks: false
        SelectedCrateTestCase::new(
            "cc",
            "1.2.16",
            Some("2025-03-13"),
            TestCrateType::function("flags::RustcCodegenFlags::<'this>::cc_flags", None),
        ), // Note: original had validity_checks: false
        SelectedCrateTestCase::new(
            "encoding_rs",
            "0.8.35",
            Some("2025-03-13"),
            TestCrateType::function("iso_2022_jp::Iso2022JpDecoder::decode_to_utf16_raw", None),
        ), // Note: original had validity_checks: false
        SelectedCrateTestCase::new(
            "serde_derive",
            "1.0.219",
            Some("2025-03-13"),
            TestCrateType::function("internals::attr::parse_lit_into_path", None),
        ), // Note: original had validity_checks: false
        SelectedCrateTestCase::new(
            "serde_derive",
            "1.0.219",
            Some("2025-03-13"),
            TestCrateType::function("internals::attr::is_cow", None),
        ), // Note: original had validity_checks: false
        SelectedCrateTestCase::new(
            "serde_derive",
            "1.0.219",
            Some("2025-03-13"),
            TestCrateType::function("internals::ast::Container::<'a>::from_ast", None),
        ), // Note: original had validity_checks: false
        SelectedCrateTestCase::new(
            "tracing-subscriber",
            "0.3.19",
            None,
            TestCrateType::EntireCrate,
        ), // Note: original had validity_checks: false
        SelectedCrateTestCase::new("rustls", "0.23.23", None, TestCrateType::EntireCrate),
    ];

    for test_case in test_cases.into_iter().sorted_by_key(|tc| {
        if let TestCrateType::Function(f) = &tc.test_type {
            if f.debug_failure {
                0 // Try these first
            } else {
                f.metadata.num_bbs.unwrap_or(usize::MAX)
            }
        } else {
            usize::MAX
        }
    }) {
        test_case.run();
    }
}
