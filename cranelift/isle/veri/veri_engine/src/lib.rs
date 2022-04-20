use cranelift_isle as isle;
use isle::sema::{TermEnv, TypeEnv};
use std::path::PathBuf;

pub mod interp;
pub mod renaming;
pub mod rule_tree;
pub mod solver;
pub mod type_check;

/// Given a file, lexes and parses the file to an ISLE term and type environment tuple
pub fn isle_files_to_terms(files: &Vec<PathBuf>) -> (TermEnv, TypeEnv) {
    let lexer = isle::lexer::Lexer::from_files(files).unwrap();
    parse_isle_to_terms(lexer)
}

/// Produces the two ISLE-defined structs with type and term environments
pub fn parse_isle_to_terms(lexer: isle::lexer::Lexer) -> (TermEnv, TypeEnv) {
    // Parses to an AST, as a list of definitions
    let defs = isle::parser::parse(lexer).expect("should parse");

    // Produces maps from symbols/names to types
    let mut typeenv = TypeEnv::from_ast(&defs).unwrap();

    // Produces a list of terms, rules, and map from symbols to terms
    let termenv = TermEnv::from_ast(&mut typeenv, &defs).unwrap();
    (termenv, typeenv)
}
