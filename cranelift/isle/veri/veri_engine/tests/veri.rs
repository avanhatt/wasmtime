use cranelift_isle as isle;
use isle::sema::Rule;
use std::env;
use std::path::PathBuf;
use veri_annotation::parser_wrapper::{parse_annotations, parse_annotations_str, AnnotationEnv};
use veri_engine_lib::interp::AssumptionContext;
use veri_engine_lib::isle_files_to_terms;
use veri_engine_lib::rule_tree::verify_rules_for_type_with_lhs_root;
use veri_ir::{all_starting_bitvectors, VIRType, VerificationResult};

mod utils;
use utils::{all_success_result, lt_64_success_result, custom_result, just_8_result};
use utils::{isle_str_to_terms, test_from_file, test_from_file_self_contained, verify_rule_for_type, test_from_file_custom_prelude};

#[test]
fn test_iadds() {
    test_from_file_custom_prelude("./tests/code/selfcontained/simple_prelude.isle",
				  "./tests/code/selfcontained/simple_iadd.isle",
				  lt_64_success_result());

    test_from_file_custom_prelude("./tests/code/selfcontained/simple_prelude.isle",
				  "./tests/code/selfcontained/iadd_to_sub.isle",
				  lt_64_success_result());
}

#[test]
fn test_implicit_conversions() {
    test_from_file_custom_prelude("./tests/code/selfcontained/prelude.isle",
				  "./tests/code/selfcontained/simple_iadd_implicit_conv.isle",
				  lt_64_success_result());

    test_from_file_custom_prelude("./tests/code/selfcontained/prelude.isle",
				  "./tests/code/selfcontained/iadd_to_sub_implicit_conv.isle",
				  lt_64_success_result());    
}

#[test]
fn test_iadd_from_file() {
    test_from_file("./examples/iadd.isle", lt_64_success_result())
}

#[test]
fn test_chained_iadd_from_file() {
    test_from_file("./examples/iadd-two-rule-chain.isle", lt_64_success_result())
}

#[test]
fn test_let() {
    test_from_file_self_contained("./tests/code/selfcontained/let.isle", just_8_result());
}
