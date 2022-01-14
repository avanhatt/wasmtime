//! Build assumptions from the left hand side of a rule.
//!

use cranelift_isle as isle;
use isle::sema::{Pattern, Rule, Term, TermArgPattern, TermEnv, TypeEnv};

/// For now, we assume the LHS of a rule matches (lower (has_type (...) (...))). 
/// This function asserts that shape.
pub fn unwrap_lower_has_type(pattern: &Pattern, termenv: &TermEnv, typeenv: &TypeEnv) {
    let lower_arg = match pattern {
        Pattern::Term(tyid, termid, arg_patterns) => {
            let term = &termenv.terms[termid.index()];
            // Outermost term is lower
            assert!(typeenv.syms[term.name.index()] == "lower");
            assert!(arg_patterns.len() == 1);
            &arg_patterns[0]

        }
        _ => unimplemented!("Expected 'lower' term"),
    };
    let has_type_args = match lower_arg {
        TermArgPattern::Pattern (Pattern::Term(tyid, termid, arg_patterns)) => {
            let term = &termenv.terms[termid.index()];
            // Outermost term is lower
            assert!(typeenv.syms[term.name.index()] == "has_type");
            assert!(arg_patterns.len() == 2);
            arg_patterns

        }
        _ => unimplemented!("Expected 'lower' term"),
    };
    dbg!(has_type_args);

}

/// Takes in LHS definitions, ty map, produces SMTLIB list
/// For now, also trying to say from (lower (... (iadd (a) (b)))), make fresh vars a b of size TYPE
pub fn parse_lhs_to_assumptions(pattern: &Pattern, termenv: &TermEnv, typeenv: &TypeEnv) {
    unwrap_lower_has_type(pattern, termenv, typeenv);
}
