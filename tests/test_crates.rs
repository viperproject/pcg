mod test_utils;

#[test]
fn check_test_crates() {
    // Create tmp directory if it doesn't exist
    std::fs::create_dir_all("tmp").unwrap();

    // Test toml_edit 0.22.23
    test_utils::run_on_crate("toml_edit", "0.22.23");
}
