use std::collections::HashMap;

use cranelift_isle as isle;
use isle::sema::{Rule, TermEnv, TypeEnv};
use itertools::Itertools;
use veri_ir::{all_starting_bitvectors, RuleSemantics, VIRType};
use veri_ir::{BoundVar, RuleTree};

use crate::interp::AssumptionContext;
use crate::pattern_term_name;
use crate::verify_rule_for_type;

pub fn build_rule_tree_rec(
    ctx: &mut AssumptionContext<'_>,
    rule: &Rule,
    termenv: &TermEnv,
    typeenv: &TypeEnv,
    ty: &VIRType,
    depth: usize,
    max_depth: usize,
) -> RuleTree {
    assert!(depth <= max_depth, "Exceeded maximum rule tree depth!");

    let rule_sem = ctx.interp_rule(rule);

    if depth == 0 {
        assert!(
            rule_sem.lhs_undefined_terms.is_empty(),
            "Cannot have undefined terms in the initial root rule, found: {:?}",
            rule_sem.lhs_undefined_terms
        );
    }

    let mut children: HashMap<BoundVar, RuleTree> = HashMap::new();
    for t in rule_sem.rhs_undefined_terms.clone().into_iter().unique() {
        for next_rule in rules_with_lhs_root(&t.name, termenv, typeenv) {
            let child =
                build_rule_tree_rec(ctx, &next_rule, termenv, typeenv, ty, depth + 1, max_depth);
            children.insert(t.clone(), child);
        }
    }

    RuleTree {
        value: rule_sem,
        children,
    }
}

pub fn build_rule_tree_from_root(
    rule: &Rule,
    termenv: &TermEnv,
    typeenv: &TypeEnv,
    ty: &VIRType,
) -> RuleTree {
    let mut ctx = AssumptionContext::new(termenv, typeenv, ty);
    build_rule_tree_rec(&mut ctx, rule, termenv, typeenv, ty, 0, 20)
}

pub fn rules_with_lhs_root(name: &str, termenv: &TermEnv, typeenv: &TypeEnv) -> Vec<Rule> {
    termenv
        .rules
        .iter()
        .filter_map(|rule| {
            if pattern_term_name(rule.lhs.clone(), termenv, typeenv) == name {
                Some(rule.clone())
            } else {
                None
            }
        })
        .collect()
}

pub fn verify_rules_with_lhs_root(root: &str, termenv: &TermEnv, typeenv: &TypeEnv) {
    for ty in all_starting_bitvectors() {
        for rule in rules_with_lhs_root(root, termenv, typeenv) {
            let rule_tree = build_rule_tree_from_root(&rule, termenv, typeenv, &ty);
            dbg!(rule_tree);
            // let _res = verify_rule_for_type(&rule, termenv, typeenv, &ty);
        }
    }
}
