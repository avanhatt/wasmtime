use veri_engine_lib::interp::AssumptionContext;
use veri_engine_lib::rule_tree::verify_rules_for_type_with_lhs_root;

use cranelift_isle as isle;
use isle::sema::Rule;
use veri_annotation::parser_wrapper::{parse_annotations_str, AnnotationEnv};
use veri_ir::{all_starting_bitvectors, VIRType, VerificationResult};

mod utils;
//use solver::run_solver_single_rule;

#[test]
fn foo () {
    assert_eq!(4, 2+2);
}
