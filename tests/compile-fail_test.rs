#[cfg(all(test, feature = "nightly_test"))]
extern crate compiletest_rs as compiletest;

#[cfg(all(test, feature = "nightly_test"))]
fn run_mode(mode: &'static str) {
    use std::path::PathBuf;

    let mut config = compiletest::default_config();
    let cfg_mode = mode.parse().ok().expect("Invalid mode");

    config.mode = cfg_mode;
    config.src_base = PathBuf::from(format!("tests/{}", mode));
    config.target_rustcflags = Some("-L target/debug".to_string());

    compiletest::run_tests(&config);
}

#[test]
#[cfg(all(test, feature = "nightly_test"))]
fn compile_test() {
    run_mode("compile-fail");
}
