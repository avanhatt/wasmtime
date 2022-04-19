//use crate::rule_tree::{verify_rules_with_lhs_root};
use clap::{Arg, Command};
use cranelift_isle as isle;
use isle::sema::{Pattern, TermEnv, TypeEnv};
use std::env;
use std::path::PathBuf;
use veri_annotation::parser_wrapper::parse_annotations;

mod interp;
mod renaming;
mod rule_tree;
mod solver;
mod type_check;

fn foo () {
    panic!()
}
