use cranelift_isle as isle;
use easy_smt::SExpr;
use isle::compile::create_envs;
use isle::sema::{TermEnv, TypeEnv};
use std::path::PathBuf;

pub mod interp;
pub mod solver;
pub mod termname;
pub mod type_inference;
pub mod verify;
pub mod widths;

pub const REG_WIDTH: usize = 64;

pub const FLAGS_WIDTH: usize = 4;

pub const WIDTHS: [usize; 4] = [8, 16, 32, 64];

pub struct Config {
    pub term: String,
    pub names: Option<Vec<String>>,
    pub dyn_width: bool,
    pub distinct_check: bool,

    pub custom_verification_condition:
        Option<Box<dyn Fn(&easy_smt::Context, Vec<SExpr>, SExpr, SExpr) -> SExpr>>,
}

/// Given a file, lexes and parses the file to an ISLE term and type environment tuple
pub fn isle_files_to_terms(files: &Vec<PathBuf>) -> (TypeEnv, TermEnv) {
    let lexer = isle::lexer::Lexer::from_files(files).unwrap();
    parse_isle_to_terms(lexer)
}

/// Produces the two ISLE-defined structs with type and term environments
pub fn parse_isle_to_terms(lexer: isle::lexer::Lexer) -> (TypeEnv, TermEnv) {
    // Parses to an AST, as a list of definitions
    let defs = isle::parser::parse(lexer).expect("should parse");

    // Produces environments including terms, rules, and maps from symbols and
    // names to types
    create_envs(&defs).unwrap()
}
