mod common;

#[test]
fn check_test_crates() {
    // Create tmp directory if it doesn't exist
    std::fs::create_dir_all("tmp").unwrap();

    // Test toml_edit 0.22.23
    common::run_on_crate("toml_edit", "0.22.23");
}
