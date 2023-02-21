use crate::type_inference::type_rules_with_term_and_types;
use crate::widths::isle_inst_types;
use cranelift_isle as isle;
use isle::compile::create_envs;
use isle::sema::{Pattern, RuleId, TermEnv, TypeEnv};
use std::collections::HashMap;
use std::path::PathBuf;
use veri_annotation::parser_wrapper::parse_annotations;

use crate::solver::run_solver;
use crate::type_inference::Solution;
use crate::{interp::Context, termname::pattern_contains_termname};
use veri_ir::{RuleSemantics, Type, VerificationResult, ConcreteTest};

pub fn verify_rules(inputs: Vec<PathBuf>, term: String, dynwidths: bool) {
    let lexer = isle::lexer::Lexer::from_files(&inputs).unwrap();

    // Parses to an AST, as a list of definitions
    let defs = isle::parser::parse(lexer).expect("should parse");

    // Produces environments including terms, rules, and maps from symbols and
    // names to types
    let (typeenv, termenv) = create_envs(&defs).unwrap();

    let annotation_env = parse_annotations(&inputs);

    // Get the types/widths for this particular term
    let types = isle_inst_types()
        .get(&term.as_str())
        .expect(format!("Missing term width for {}", term).as_str())
        .clone();

    for type_instantiation in types {
        let type_sols = type_rules_with_term_and_types(
            defs.clone(),
            &termenv,
            &typeenv,
            &annotation_env,
            &term,
            &type_instantiation,
        );
        verify_rules_for_term(
            &termenv,
            &typeenv,
            &type_sols,
            &term,
            type_instantiation,
            dynwidths,
            &None,
        );
    }
}

pub fn verify_rules_for_term(
    termenv: &TermEnv,
    typeenv: &TypeEnv,
    typesols: &HashMap<RuleId, Solution>,
    term: &String,
    types: Vec<Type>,
    dynwidths: bool,
    concrete: &Option<ConcreteTest>
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
            &term,
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
        let sol = &ctx.typesols[&rule.id];
        let rule_sem = RuleSemantics {
            lhs: sol.lhs.clone(),
            rhs: sol.rhs.clone(),
            assumptions: sol.assumptions.clone(),
            quantified_vars: sol.quantified_vars.clone(),
            free_vars: sol.free_vars.clone(),
            tyctx: sol.tyctx.to_owned(),
        };
        println!("Verifying rule with term {term} and types {:?}", types);
        let result = run_solver(rule_sem, rule, termenv, typeenv, dynwidths, concrete);
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
