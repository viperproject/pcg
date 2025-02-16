mod common;

#[test]
fn check_test_crates() {
    // Create tmp directory if it doesn't exist
    std::fs::create_dir_all("tmp").unwrap();

    // common::run_on_crate("zerovec-derive", "0.10.3", true);
    // common::run_on_crate("toml_edit", "0.22.23", false);
}
