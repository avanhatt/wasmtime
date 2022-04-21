use veri_engine_lib::interp::AssumptionContext;
use veri_engine_lib::rule_tree::verify_rules_for_type_with_lhs_root;
use veri_engine_lib::solver::run_solver_single_rule;
use veri_engine_lib::{isle_files_to_terms, parse_isle_to_terms};
use cranelift_isle as isle;
use isle::sema::{Rule, TermEnv, TypeEnv};
use veri_annotation::parser_wrapper::{parse_annotations_str, parse_annotations, AnnotationEnv};
use veri_ir::{all_starting_bitvectors, VIRType, VerificationResult};
use std::path::PathBuf;
use std::env;

pub enum Bitwidth {
    I1,
    I8,
    I16,
    I32,
    I64,
    I128,
}

pub enum RangeInfo {
    Inclusive,
    Exclusive,
}

pub struct TestRange {
    pub start: Bitwidth,
    pub start_range: RangeInfo,
    pub end: Bitwidth,
    pub end_range: RangeInfo, 
}


pub fn all_widths() -> TestRange {
    TestRange {
	start: Bitwidth::I1,
	start_range: RangeInfo::Inclusive,
	end: Bitwidth::I128,
	end_range: RangeInfo::Inclusive,
    }
}

pub fn verify_rule_for_type(
    rule: &Rule,
    termenv: &TermEnv,
    typeenv: &TypeEnv,
    annotation_env: &AnnotationEnv,
    ty: &VIRType,
) -> VerificationResult {
    // For now, starting types must be bitvectors
    assert!(ty.is_bv());
    let mut ctx = AssumptionContext::new(termenv, typeenv, annotation_env, ty);
    let rule_semantics = ctx.interp_rule(rule);
    run_solver_single_rule(rule_semantics, ty)
}

pub fn isle_str_to_terms(s: &str) -> (TermEnv, TypeEnv) {
    let lexer = isle::lexer::Lexer::from_str(s, "input.isle").unwrap();
    parse_isle_to_terms(lexer)
}

pub fn test_from_file(s: &str, range: TestRange) -> () {
    let cur_dir = env::current_dir().expect("Can't access current working directory");
    // TODO: clean up path logic
    let clif_isle = cur_dir.join("../../../codegen/src").join("clif.isle");
    let prelude_isle = cur_dir.join("../../../codegen/src").join("prelude.isle");
    let input = PathBuf::from(s);

    let inputs = vec![clif_isle, prelude_isle, input];
    
    let (termenv, typeenv) = isle_files_to_terms(&inputs);
    let annotation_env = parse_annotations(&inputs);
    
    // For now, verify rules rooted in `lower`
    for ty in all_starting_bitvectors() {
        // The expected result is based on whether the type matches fits_in_64
        let expected_result = if ty.clone().width() <= 64 {
            VerificationResult::Success
        } else {
            VerificationResult::InapplicableRule
        };
        let result = verify_rules_for_type_with_lhs_root("lower", &termenv, &typeenv, &annotation_env, &ty);
        assert_eq!(result, expected_result);
    }
}

pub fn test_from_file_self_contained(s: &str) -> () {

}
