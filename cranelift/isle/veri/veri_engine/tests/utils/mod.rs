use cranelift_isle as isle;
use isle::sema::{Rule, TermEnv, TypeEnv};
use std::env;
use std::path::PathBuf;
use strum::IntoEnumIterator;
use strum_macros::EnumIter;
use veri_annotation::parser_wrapper::{parse_annotations, parse_annotations_str, AnnotationEnv};
use veri_engine_lib::interp::AssumptionContext;
use veri_engine_lib::rule_tree::verify_rules_for_type_with_lhs_root;
use veri_engine_lib::solver::run_solver_single_rule;
use veri_engine_lib::{isle_files_to_terms, parse_isle_to_terms};
use veri_ir::{all_starting_bitvectors, VIRType, VerificationResult};

#[derive(Debug, EnumIter, PartialEq, Eq, PartialOrd, Ord, Copy, Clone)]
pub enum Bitwidth {
    I1 = 1,
    I8 = 8,
    I16 = 16,
    I32 = 32,
    I64 = 64,
    I128 = 128,
}

type Result = (Bitwidth, VerificationResult);
type TestResult = Vec<Result>;

pub fn all_success() -> TestResult {
    Bitwidth::iter()
        .map(|w| (w, VerificationResult::Success))
        .collect()
}

pub fn lt_64_success() -> TestResult {
    Bitwidth::iter()
        .map(|w| {
            (
                w,
                if w as usize <= 64 {
                    VerificationResult::Success
                } else {
                    VerificationResult::InapplicableRule
                },
            )
        })
        .collect()
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

pub fn test_from_file(s: &str, tr: TestResult) -> () {
    let cur_dir = env::current_dir().expect("Can't access current working directory");
    // TODO: clean up path logic
    let clif_isle = cur_dir.join("../../../codegen/src").join("clif.isle");
    let prelude_isle = cur_dir.join("../../../codegen/src").join("prelude.isle");
    let input = PathBuf::from(s);

    let inputs = vec![clif_isle, prelude_isle, input];

    let (termenv, typeenv) = isle_files_to_terms(&inputs);
    let annotation_env = parse_annotations(&inputs);

    // For now, verify rules rooted in `lower`
    for (bw, expected_result) in tr {
        let result = verify_rules_for_type_with_lhs_root(
            "lower",
            &termenv,
            &typeenv,
            &annotation_env,
            &VIRType::BitVector(bw as usize),
        );
        assert_eq!(result, expected_result);
    }
}

pub fn test_from_file_self_contained(s: &str) -> () {}
