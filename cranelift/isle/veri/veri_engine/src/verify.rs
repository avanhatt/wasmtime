use crate::type_inference::type_rules_with_term_and_types;
use crate::widths::isle_inst_types;
use crate::Config;
use cranelift_isle as isle;
use isle::compile::create_envs;
use isle::sema::{Pattern, RuleId, TermEnv, TypeEnv};
use std::collections::HashMap;
use std::path::PathBuf;
use veri_annotation::parser_wrapper::parse_annotations;

use crate::solver::run_solver;
use crate::type_inference::RuleSemantics;
use crate::{interp::Context, termname::pattern_contains_termname};
use veri_ir::{ConcreteTest, Type, VerificationResult};

pub fn verify_rules(inputs: Vec<PathBuf>, config: &Config) {
    let lexer = isle::lexer::Lexer::from_files(&inputs).unwrap();

    // Parses to an AST, as a list of definitions
    let defs = isle::parser::parse(lexer).expect("should parse");

    // Produces environments including terms, rules, and maps from symbols and
    // names to types
    let (typeenv, termenv) = create_envs(&defs).unwrap();

    let annotation_env = parse_annotations(&inputs);

    // Get the types/widths for this particular term
    let types = isle_inst_types()
        .get(&config.term as &str)
        .expect(format!("Missing term width for {}", config.term).as_str())
        .clone();

    for type_instantiation in types {
        let type_sols = type_rules_with_term_and_types(
            defs.clone(),
            &termenv,
            &typeenv,
            &annotation_env,
            &config.term,
            &type_instantiation,
            &None,
        );
        verify_rules_for_term(
            &termenv,
            &typeenv,
            &type_sols,
            type_instantiation,
            &None,
            config,
        );
    }
}

pub fn verify_rules_for_term(
    termenv: &TermEnv,
    typeenv: &TypeEnv,
    typesols: &HashMap<RuleId, RuleSemantics>,
    types: Vec<Type>,
    concrete: &Option<ConcreteTest>,
    config: &Config,
) -> VerificationResult {
    let mut rules_checked = 0;
    for rule in &termenv.rules {
        // Only type rules with the given term on the LHS
        if !pattern_contains_termname(
            // Hack for now: typeid not used
            &Pattern::Term(
                cranelift_isle::sema::TypeId(0),
                rule.root_term,
                rule.args.clone(),
            ),
            &config.term,
            termenv,
            typeenv,
        ) {
            log::debug!("skipping rule that doesn't meet filter");
            continue;
        }
        let ctx = Context::new(typesols);
        if ctx.typesols.get(&rule.id).is_none() {
            continue;
        }
        let rule_sem = &ctx.typesols[&rule.id];
        println!(
            "Verifying rule with term {} and types {:?}",
            config.term, types
        );
        let result = run_solver(rule_sem, rule, termenv, typeenv, concrete, config);
        rules_checked += 1;
        if result != VerificationResult::Success {
            return result;
        }
    }
    if rules_checked > 0 {
        VerificationResult::Success
    } else {
        panic!("No rules checked!")
    }
}
