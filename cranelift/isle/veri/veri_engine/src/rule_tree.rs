use std::collections::HashMap;

use cranelift_isle as isle;
use isle::sema::{Rule, TermEnv, TypeEnv};
use itertools::Itertools;
use veri_ir::{all_starting_bitvectors, VIRType, VIRExpr, RuleSemantics, BoundVar, RuleTree, RulePath};

use crate::interp::AssumptionContext;
use crate::pattern_term_name;
use crate::solver::run_solver_rule_path;

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

/// Enumerate all paths from root to leaves. Note: this is not optimized for
/// efficiency, values are cloned for each path.
pub fn enumerate_paths_to_leaves(tree: &RuleTree) -> Vec<RulePath> {
    // Leaf base case
    if tree.children.is_empty() {
        return vec![RulePath {
            rules: vec![tree.value.clone()],
            undefined_terms: vec![],
        }]
    }

    let mut all_paths = vec![];
    for (term, child) in &tree.children {
        let paths = enumerate_paths_to_leaves(&child);
        for path in paths {
            let mut rules = path.rules.clone();
            rules.insert(0, tree.value.clone());
            let mut undefined_terms = path.undefined_terms.clone();
            undefined_terms.insert(0, term.clone());
            all_paths.push(RulePath {rules, undefined_terms})
        }
    }
    all_paths
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
            let paths = enumerate_paths_to_leaves(&rule_tree);
            for rule_path in paths {
                let result = run_solver_rule_path(rule_path);

            }
            // dbg!(paths.iter().map(|sem| sem.lhs.clone()).collect::<Vec<VIRExpr>>());
            // dbg!(rule_tree);
            // let _res = verify_rule_for_type(&rule, termenv, typeenv, &ty);
        }
    }
}
