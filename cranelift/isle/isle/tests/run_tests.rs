//! Helper for autogenerated unit tests.

use cranelift_isle::compile;
use cranelift_isle::error::Errors;
use std::default::Default;

fn build(filename: &str) -> Result<String, Errors> {
    compile::from_files(&[filename], &Default::default())
}

fn envs_for_analysis(filename: &str) -> Result<(TypeEnv, TermEnv)> {
    let lexer = lexer::Lexer::from_files(vec![filename])?;
    let defs = parser::parse(lexer)?;
    compile::create_envs(&defs)
}

pub fn run_pass(filename: &str) {
    if let Err(err) = build(filename) {
        panic!("pass test failed:\n{:?}", err);
    }
}

pub fn run_fail(filename: &str) {
    if build(filename).is_ok() {
        panic!("test {} passed unexpectedly", filename);
    }
}

fn build_and_link_isle(isle_filename: &str) -> (tempfile::TempDir, std::path::PathBuf) {
    let tempdir = tempfile::tempdir().unwrap();
    let code = build(isle_filename).unwrap();

    let isle_filename_base = std::path::Path::new(isle_filename)
        .file_stem()
        .unwrap()
        .to_str()
        .unwrap()
        .to_string();
    let isle_generated_code = tempdir
        .path()
        .to_path_buf()
        .join(isle_filename_base.clone() + ".rs");
    std::fs::write(isle_generated_code, code).unwrap();

    let rust_filename = isle_filename.replace(".isle", "").to_string() + "_main.rs";
    let rust_filename_base = std::path::Path::new(&rust_filename).file_name().unwrap();
    let rust_driver = tempdir.path().to_path_buf().join(&rust_filename_base);
    println!("copying {} to {:?}", rust_filename, rust_driver);
    std::fs::copy(&rust_filename, &rust_driver).unwrap();

    let output = tempdir.path().to_path_buf().join("out");

    let mut rustc = std::process::Command::new("rustc")
        .arg(&rust_driver)
        .arg("-o")
        .arg(output.clone())
        .spawn()
        .unwrap();
    assert!(rustc.wait().unwrap().success());

    (tempdir, output)
}

pub fn run_link(isle_filename: &str) {
    build_and_link_isle(isle_filename);
}

pub fn run_run(isle_filename: &str) {
    let (_tempdir, exe) = build_and_link_isle(isle_filename);

    assert!(std::process::Command::new(exe)
        .spawn()
        .unwrap()
        .wait()
        .unwrap()
        .success());
}

pub fn run_envs_for_analysis(filename: &str) {
    match envs_for_analysis(filename) {
        // Alexa TODO: is there a more general check that the term was not expanded?
        Ok((typeenv, termenv)) => {
            assert!(termenv
                .terms
                .iter()
                .any(|t| typeenv.syms[t.name.index()] == "isub"))
        }
        Err(e) => panic!("envs_for_analysis failed {:?}", e),
    }
}

// Generated by build.rs.
include!(concat!(env!("OUT_DIR"), "/isle_tests.rs"));
