use std::collections::HashMap;

use cranelift_isle as isle;
use isle::sema::{Rule, TermEnv, TypeEnv};
use itertools::Itertools;
use veri_ir::{all_starting_bitvectors, RuleSemantics, VIRType};
use veri_ir::{BoundVar, RuleTree};

use crate::interp::AssumptionContext;
use crate::pattern_term_name;
use crate::verify_rule_for_type;

/// Recursively build a rule tree of possible rewrites, connected by undefined
/// terms on the left hand sides (LHS) and right hand sides (RHS). 
pub fn build_rule_tree_rec(
    ctx: &mut AssumptionContext<'_>,
    rule: &Rule,
    termenv: &TermEnv,
    typeenv: &TypeEnv,
    ty: &VIRType,
    depth: usize,
    max_depth: usize,
) -> RuleTree {
    // Basic sanity check to avoid infinite cycles, might want to add actual
    // cycle checking later.
    assert!(depth <= max_depth, "Exceeded maximum rule tree depth!");

    // Get the semantics for this specific rule
    let rule_sem = ctx.interp_rule(rule);

    // If we are at the root of the tree, we should not have any undefined
    // terms on the left hand side
    if depth == 0 {
        assert!(
            rule_sem.lhs_undefined_terms.is_empty(),
            "Cannot have undefined terms in the LHS of the initial root rule, found: {:?}",
            rule_sem.lhs_undefined_terms
        );
    }

    // Recur: if any RHS term is undefined, add a child for each possible next
    // rule. Also track the height of the tree.
    let mut children: HashMap<BoundVar, RuleTree> = HashMap::new();
    let mut max_height = 0;
    for t in rule_sem.rhs_undefined_terms.clone().into_iter().unique() {
        let next_rules = rules_with_lhs_root(&t.name, termenv, typeenv);

        // Since we are not at a leaf node (because there are undefined terms
        // on the RHS), we need next rules for any of the terms currently 
        // undefined (which by definition lack annotations).
        assert!(
            !next_rules.is_empty(),
            "Missing annotation or next rules for unknown term  {:?}",
            t.name
        );
        for next_rule in rules_with_lhs_root(&t.name, termenv, typeenv) {
            let child =
                build_rule_tree_rec(ctx, &next_rule, termenv, typeenv, ty, depth + 1, max_depth);
            if child.height > max_height {
                max_height = child.height;
            }
            children.insert(t.clone(), child);
        }
    }

    RuleTree {
        value: rule_sem,
        children,
        height: max_height + 1,
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
            // dbg!(rule_tree);
            // let _res = verify_rule_for_type(&rule, termenv, typeenv, &ty);
        }
    }
}
