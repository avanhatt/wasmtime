use std::env;
use std::path::PathBuf;
use strum::IntoEnumIterator;
use strum_macros::EnumIter;
use veri_ir::{VIRType, VerificationResult};
use veri_annotation::parser_wrapper::parse_annotations;
use veri_engine_lib::isle_files_to_terms; // parse_isle_to_terms};
use veri_engine_lib::rule_tree::verify_rules_for_type_with_lhs_root;

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
type TestResultBuilder = dyn Fn(Bitwidth) -> (Bitwidth, VerificationResult);

// Some examples of functions we might need

pub fn just_8_result() -> TestResult {
    vec![(Bitwidth::I8, VerificationResult::Success)]
}

#[allow(dead_code)]
pub fn just_16_result() -> TestResult {
    vec![(Bitwidth::I16, VerificationResult::Success)]
}

#[allow(dead_code)]
pub fn just_32_result() -> TestResult {
    vec![(Bitwidth::I32, VerificationResult::Success)]
}

#[allow(dead_code)]
pub fn just_64_result() -> TestResult {
    vec![(Bitwidth::I64, VerificationResult::Success)]
}

#[allow(dead_code)]
pub fn just_128_result() -> TestResult {
    vec![(Bitwidth::I128, VerificationResult::Success)]
}

/// All bitwidths verify
#[allow(dead_code)]
pub fn all_success_result() -> TestResult {
    custom_result(&|w| (w, VerificationResult::Success))
}

/// Only bitwidths under and including 64 should verify, rest inapplicable
pub fn lt_64_success_result() -> TestResult {
    custom_result(&|w| {
        (
            w,
            if w as usize <= 64 {
                VerificationResult::Success
            } else {
                VerificationResult::InapplicableRule
            },
        )
    })
}

/// Specify a custom set expected result (helpful if you want to test all the bitwidths and expect
/// a range of different success, failure, and inapplicable outcomes)
pub fn custom_result(f: &TestResultBuilder) -> TestResult {
    Bitwidth::iter().map(|w| f(w)).collect()
}

// May want this again
// pub fn isle_str_to_terms(s: &str) -> (TermEnv, TypeEnv) {
//     let lexer = isle::lexer::Lexer::from_str(s, "input.isle").unwrap();
//     parse_isle_to_terms(lexer)
// }

// TODO: waiting on output thoughts. re do previous?
fn test(inputs: Vec<PathBuf>, tr: TestResult) -> () {
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

pub fn test_from_file(s: &str, tr: TestResult) -> () {
    // TODO: clean up path logic
    let cur_dir = env::current_dir().expect("Can't access current working directory");
    let clif_isle = cur_dir.join("../../../codegen/src").join("clif.isle");
    let prelude_isle = cur_dir.join("../../../codegen/src").join("prelude.isle");
    let input = PathBuf::from(s);
    test(vec![clif_isle, prelude_isle, input], tr);
}

pub fn test_from_file_self_contained(s: &str, tr: TestResult) -> () {
    let input = PathBuf::from(s);
    test(vec![input], tr);
}

pub fn test_from_file_custom_prelude(p: &str, s: &str, tr: TestResult) -> () {
    let prelude = PathBuf::from(p);
    let input = PathBuf::from(s);
    test(vec![prelude, input], tr);
}
