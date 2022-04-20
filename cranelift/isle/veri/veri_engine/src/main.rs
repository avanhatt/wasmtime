//! Prototype verification tool for Cranelift's ISLE lowering rules.

use clap::{Arg, Command};
use std::env;
use std::path::PathBuf;
use veri_annotation::parser_wrapper::parse_annotations;
use veri_engine_lib::rule_tree::verify_rules_with_lhs_root;
use veri_engine_lib::isle_files_to_terms;

fn main() {
    let cur_dir = env::current_dir().expect("Can't access current working directory");

    // TODO: clean up path logic
    let clif_isle = cur_dir.join("../../../codegen/src").join("clif.isle");
    let prelude_isle = cur_dir.join("../../../codegen/src").join("prelude.isle");

    // Disable for now to not have to consider all rules
    // let aarch64_isle = cur_dir.join("../../../codegen/src/isa/aarch64").join("inst.isle");

    let matches = Command::new("Verification Engine for ISLE")
        .arg(
            Arg::new("INPUT")
                .help("Sets the input file")
                .required(true)
                .index(1),
        )
        .get_matches();
    let input = PathBuf::from(matches.value_of("INPUT").unwrap());

    let inputs = vec![clif_isle, prelude_isle, input];

    let (termenv, typeenv) = isle_files_to_terms(&inputs);
    let annotation_env = parse_annotations(&inputs);

    // For now, verify rules rooted in `lower`
    verify_rules_with_lhs_root("lower", &termenv, &typeenv, &annotation_env);
}
