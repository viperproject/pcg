use std::process::Command;

fn main() {
    let sysroot = Command::new("rustc")
        .arg("--print")
        .arg("sysroot")
        .output()
        .expect("Failed to get sysroot")
        .stdout;

    let sysroot_path = String::from_utf8(sysroot).expect("Invalid UTF-8").trim().to_string();

    println!("cargo:rustc-link-arg=-Wl,-rpath,{}/lib", sysroot_path);
}
