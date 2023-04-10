use cranelift_isle::compile::create_envs;
use std::env;
use std::path::PathBuf;
use std::time::Duration;
use strum::IntoEnumIterator;
use strum_macros::EnumIter;
use veri_annotation::parser_wrapper::parse_annotations;
use veri_engine_lib::type_inference::type_rules_with_term_and_types;
use veri_engine_lib::verify::verify_rules_for_term;
use veri_engine_lib::widths::isle_inst_types;
use veri_engine_lib::Config;
use veri_ir::{ConcreteTest, Counterexample, TermSignature, VerificationResult};

#[derive(Debug, EnumIter, PartialEq, Eq, PartialOrd, Ord, Copy, Clone)]
pub enum Bitwidth {
    I8 = 8,
    I16 = 16,
    I32 = 32,
    I64 = 64,
}

type Result = (Bitwidth, VerificationResult);
type TestResult = Vec<Result>;
type TestResultBuilder = dyn Fn(Bitwidth) -> (Bitwidth, VerificationResult);

// Some examples of functions we might need
#[allow(dead_code)]
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

/// All bitwidths verify
#[allow(dead_code)]
pub fn all_success_result() -> TestResult {
    custom_result(&|w| (w, VerificationResult::Success))
}

/// All bitwidths fail
#[allow(dead_code)]
pub fn all_failure_result() -> TestResult {
    custom_result(&|w| (w, VerificationResult::Failure(Counterexample {})))
}

/// Only bitwidths under and including 64 should verify, rest inapplicable
pub fn lte_64_success_result() -> TestResult {
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

/// Run the test with a 4 minute timeout, retrying 5 times if timeout hit, waiting 1ms between tries
pub fn run_and_retry<F>(f: F) -> ()
where
    F: Fn() -> (),
    F: Send + 'static + Copy,
{
    let delay_before_retrying = retry::delay::Fixed::from_millis(1);
    let num_retries = 5;
    let timeout_per_try = Duration::from_secs(4 * 60);

    use std::{sync::mpsc, thread};
    let result = retry::retry_with_index(delay_before_retrying, |current_try| {
        if current_try > num_retries {
            return retry::OperationResult::Err(format!(
                "Test did not succeed within {} tries",
                num_retries
            ));
        }
        if current_try > 1 {
            println!("Retrying test that timed out, try #{}", current_try);
        }

        // From: https://github.com/rust-lang/rfcs/issues/2798
        let (done_tx, done_rx) = mpsc::channel();
        let handle = thread::spawn(move || {
            f();
            done_tx.send(()).expect("Unable to send completion signal");
        });

        match done_rx.recv_timeout(timeout_per_try) {
            Ok(_) => match handle.join() {
                Ok(_) => retry::OperationResult::Ok("Test thread succeeded"),
                Err(e) => retry::OperationResult::Err(format!("Test thread panicked {:?}", e)),
            },
            Err(_) => match handle.join() {
                Ok(_) => retry::OperationResult::Retry("Test thread took too long".to_string()),
                Err(e) => retry::OperationResult::Err(format!("Test thread panicked {:?}", e)),
            },
        }
    });
    result.unwrap();
}

fn test_rules_with_term(inputs: Vec<PathBuf>, tr: TestResult, config: Config) -> () {
    let lexer = cranelift_isle::lexer::Lexer::from_files(&inputs).unwrap();
    let defs = cranelift_isle::parser::parse(lexer).expect("should parse");
    let (typeenv, termenv) = create_envs(&defs).unwrap();
    let annotation_env = parse_annotations(&inputs);

    // Get the types/widths for this particular term
    let types = isle_inst_types()
        .get(config.term.as_str())
        .expect(format!("Missing term width for {}", config.term).as_str())
        .clone();

    for type_instantiation in &types {
        let ty = type_instantiation.canonical_type.unwrap();
        let all_expected: Vec<&(Bitwidth, VerificationResult)> = tr
            .iter()
            .filter(|(bw, _)| match *bw {
                Bitwidth::I8 => ty == veri_ir::Type::BitVector(Some(8)),
                Bitwidth::I16 => ty == veri_ir::Type::BitVector(Some(16)),
                Bitwidth::I32 => ty == veri_ir::Type::BitVector(Some(32)),
                Bitwidth::I64 => ty == veri_ir::Type::BitVector(Some(64)),
            })
            .collect();
        if !(all_expected.len() > 0) {
            println!(
                "WARNING: type instantiation {:?} not checked in this test!",
                type_instantiation
            )
        }
        for expected in all_expected {
            let (_, expected_result) = expected;
            println!("Expected result: {:?}", expected_result);
            let type_sols = type_rules_with_term_and_types(
                defs.clone(),
                &termenv,
                &typeenv,
                &annotation_env,
                &config,
                type_instantiation,
                &None,
            );
            let result = verify_rules_for_term(
                &termenv,
                &typeenv,
                &type_sols,
                type_instantiation.clone(),
                &None,
                &config,
            );
            assert_eq!(result, *expected_result);
        }
    }
}

pub fn test_from_file_with_lhs_termname(file: &str, termname: String, tr: TestResult) -> () {
    println!("Verifying {} rules in file: {}", termname, file);
    // TODO: clean up path logic
    let cur_dir = env::current_dir().expect("Can't access current working directory");
    let clif_isle = cur_dir.join("../../../codegen/src").join("clif_lower.isle");
    let prelude_isle = cur_dir.join("../../../codegen/src").join("prelude.isle");
    let prelude_lower_isle = cur_dir
        .join("../../../codegen/src")
        .join("prelude_lower.isle");
    let mut inputs = vec![prelude_isle, prelude_lower_isle, clif_isle];
    inputs.push(PathBuf::from(file));
    let config = Config {
        dyn_width: false,
        term: termname,
        distinct_check: true,
        custom_verification_condition: None,
        names: None,
    };
    test_rules_with_term(inputs, tr, config);
}

pub fn test_aarch64_rule_with_lhs_termname(rulename: &str, termname: &str, tr: TestResult) -> () {
    println!("Verifying rule `{}` with termname {} ", rulename, termname);
    // TODO: clean up path logic
    let cur_dir = env::current_dir().expect("Can't access current working directory");
    let clif_isle = cur_dir.join("../../../codegen/src").join("clif_lower.isle");
    let prelude_isle = cur_dir.join("../../../codegen/src").join("prelude.isle");
    let prelude_lower_isle = cur_dir
        .join("../../../codegen/src")
        .join("prelude_lower.isle");
    let mut inputs = vec![prelude_isle, prelude_lower_isle, clif_isle];
    inputs.push(
        cur_dir
            .join("../../../codegen/src/isa/aarch64")
            .join("inst.isle"),
    );
    inputs.push(
        cur_dir
            .join("../../../codegen/src/isa/aarch64")
            .join("lower.isle"),
    );
    let config = Config {
        dyn_width: false,
        term: termname.to_string(),
        distinct_check: true,
        custom_verification_condition: None,
        names: Some(vec![rulename.to_string()]),
    };
    test_rules_with_term(inputs, tr, config);
}

pub fn test_from_file_with_config(file: &str, config: Config, tr: TestResult) -> () {
    println!("Verifying {} rules in file: {}", config.term, file);
    // TODO: clean up path logic
    let cur_dir = env::current_dir().expect("Can't access current working directory");
    let clif_isle = cur_dir.join("../../../codegen/src").join("clif_lower.isle");
    let prelude_isle = cur_dir.join("../../../codegen/src").join("prelude.isle");
    let prelude_lower_isle = cur_dir
        .join("../../../codegen/src")
        .join("prelude_lower.isle");
    let mut inputs = vec![prelude_isle, prelude_lower_isle, clif_isle];
    inputs.push(PathBuf::from(file));
    test_rules_with_term(inputs, tr, config);
}

pub fn test_concrete_input_from_file_with_lhs_termname(
    file: &str,
    termname: String,
    dynwidth: bool,
    concrete: ConcreteTest,
) -> () {
    println!(
        "Verifying concrete input {} rule in file: {}",
        termname, file
    );
    // TODO: clean up path logic
    let cur_dir = env::current_dir().expect("Can't access current working directory");
    let clif_isle = cur_dir.join("../../../codegen/src").join("clif_lower.isle");
    let prelude_isle = cur_dir.join("../../../codegen/src").join("prelude.isle");
    let prelude_lower_isle = cur_dir
        .join("../../../codegen/src")
        .join("prelude_lower.isle");
    let mut inputs = vec![prelude_isle, prelude_lower_isle, clif_isle];
    inputs.push(PathBuf::from(file));

    let lexer = cranelift_isle::lexer::Lexer::from_files(&inputs).unwrap();
    let defs = cranelift_isle::parser::parse(lexer).expect("should parse");
    let (typeenv, termenv) = create_envs(&defs).unwrap();
    let annotation_env = parse_annotations(&inputs);

    let config = Config {
        dyn_width: dynwidth,
        term: termname.clone(),
        distinct_check: false,
        custom_verification_condition: None,
        names: None,
    };

    // Get the types/widths for this particular term
    let args = concrete.args.iter().map(|i| i.ty.clone()).collect();
    let ret = concrete.output.ty;
    let t = TermSignature {
        args,
        ret,
        canonical_type: None,
    };

    let type_sols = type_rules_with_term_and_types(
        defs.clone(),
        &termenv,
        &typeenv,
        &annotation_env,
        &config,
        &t,
        &Some(concrete.clone()),
    );
    let result = verify_rules_for_term(&termenv, &typeenv, &type_sols, t, &Some(concrete), &config);
    assert_eq!(result, VerificationResult::Success);
}

pub fn test_from_file_with_lhs_termname_dynwidth(
    file: &str,
    termname: String,
    tr: TestResult,
) -> () {
    println!("Verifying {} rules in file: {}", termname, file);
    // TODO: clean up path logic
    let cur_dir = env::current_dir().expect("Can't access current working directory");
    let clif_isle = cur_dir.join("../../../codegen/src").join("clif_lower.isle");
    let prelude_isle = cur_dir.join("../../../codegen/src").join("prelude.isle");
    let prelude_lower_isle = cur_dir
        .join("../../../codegen/src")
        .join("prelude_lower.isle");
    let mut inputs = vec![prelude_isle, prelude_lower_isle, clif_isle];
    inputs.push(PathBuf::from(file));
    let config = Config {
        dyn_width: true,
        term: termname.clone(),
        distinct_check: false,
        custom_verification_condition: None,
        names: None,
    };
    test_rules_with_term(inputs, tr, config);
}

// pub fn test_from_file_self_contained(s: &str, tr: TestResult) -> () {
//     let input = PathBuf::from(s);
//     test(vec![input], tr);
// }

// pub fn test_from_file_custom_prelude(p: &str, s: &str, tr: TestResult) -> () {
//     let prelude = PathBuf::from(p);
//     let input = PathBuf::from(s);
//     test(vec![prelude, input], tr);
// }
