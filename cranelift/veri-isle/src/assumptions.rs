//! Build assumptions from the left hand side of a rule.
//!

use crate::context::{AssumptionContext, Var};
use crate::types::SMTType;
use cranelift_isle as isle;
use isle::sema::{Expr, Pattern, Rule, Term, TermArgPattern, TermEnv, TypeEnv};

impl AssumptionContext {
    fn assumption_for_has_type(
        &mut self,
        pattern: &Pattern,
        termenv: &TermEnv,
        typeenv: &TypeEnv,
        ty: SMTType,
    ) {
        match pattern {
            Pattern::Term(tyid, termid, arg_patterns) => {
                let term = &termenv.terms[termid.index()];
                let term_name = &typeenv.syms[term.name.index()];
                dbg!(&arg_patterns);

                match &arg_patterns[..] {
                    [TermArgPattern::Pattern(Pattern::BindPattern(tyid, varid, subpattern))] => {
                        dbg!(subpattern);
                    },
                    _ => (),
                };

                // For now, hard-code some cases we care about
                match term_name.as_ref() {
                    "fits_in_64" =>  {

                    },
                    _ => panic!("Unknown subterm for `has_type`"),
                }
            }
            _ => panic!("Expected 'lower' term"),
        };
    }

    /// Takes in LHS definitions, ty map, produces SMTLIB list
    /// For now, also trying to say from (lower (... (iadd (a) (b)))), make fresh vars a b of size TYPE
    fn parse_lhs_to_assumptions(
        &mut self,
        pattern: &Pattern,
        termenv: &TermEnv,
        typeenv: &TypeEnv,
        ty: SMTType,
    ) {
        let (ty_pattern, inst_pattern) = unwrap_lower_has_type(pattern, termenv, typeenv);
        self.assumption_for_has_type(&ty_pattern, termenv, typeenv, ty);
    }

    /// Construct the term environment from the AST and the type environment.
    pub fn from_lhs(
        lhs: &Pattern,
        termenv: &TermEnv,
        typeenv: &TypeEnv,
        ty: SMTType,
    ) -> AssumptionContext {
        let mut ctx = AssumptionContext {
            quantified_vars: vec![],
            assumptions: vec![],
        };
        ctx.parse_lhs_to_assumptions(lhs, termenv, typeenv, ty);
        ctx
    }
}

/// For now, we assume the LHS of a rule matches (lower (has_type (...) (...))).
/// This function asserts that shape and returns the type and inst arguments to has_type.
/// TODO: should probably have lifetime instead of cloning
fn unwrap_lower_has_type(
    pattern: &Pattern,
    termenv: &TermEnv,
    typeenv: &TypeEnv,
) -> (Pattern, Pattern) {
    let lower_arg = match pattern {
        Pattern::Term(tyid, termid, arg_patterns) => {
            let term = &termenv.terms[termid.index()];
            // Outermost term is lower
            assert!(typeenv.syms[term.name.index()] == "lower");
            assert!(arg_patterns.len() == 1, "expected single argument to lower");
            &arg_patterns[0]
        }
        _ => panic!("Expected 'lower' term"),
    };
    match lower_arg {
        TermArgPattern::Pattern(Pattern::Term(tyid, termid, arg_patterns)) => {
            let term = &termenv.terms[termid.index()];
            // Outermost term is lower
            assert!(typeenv.syms[term.name.index()] == "has_type");
            match &arg_patterns[..] {
                [TermArgPattern::Pattern(ty_pattern), TermArgPattern::Pattern(inst_pattern)] => {
                    (ty_pattern.clone(), inst_pattern.clone())
                }
                _ => panic!("Expected has_type!"),
            }
        }
        _ => panic!("Expected 'lower' term"),
    }
}
