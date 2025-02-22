mod common;

#[test]
fn test_selected_crates() {
    // Create tmp directory if it doesn't exist
    std::fs::create_dir_all("tmp").unwrap();

    // common::run_on_crate("proc-macro2", "1.0.93", false);
    // common::run_on_crate("wasm-bindgen-backend", "0.2.100", true);
    // common::run_on_crate("futures-util", "0.3.31", false);
    // common::run_on_crate("zerovec-derive", "0.10.3", true);
    // common::run_on_crate("toml_edit", "0.22.23", false);
}
