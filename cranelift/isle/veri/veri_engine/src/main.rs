//! Prototype verification tool for Cranelift's ISLE lowering rules.

use clap::{Arg, Command};
use cranelift_isle as isle;
use isle::sema::{Pattern, Rule, TermEnv, TypeEnv};
use std::env;
use std::path::PathBuf;
use veri_ir::{all_starting_bitvectors, VIRType, VerificationResult};

use crate::external_semantics::run_solver;
use crate::interp::AssumptionContext;

mod external_semantics;
mod interp;
mod isle_annotations;
mod renaming;

fn isle_str_to_terms(s: &str) -> (TermEnv, TypeEnv) {
    let lexer = isle::lexer::Lexer::from_str(s, "input.isle").unwrap();
    parse_isle_to_terms(lexer)
}

fn isle_files_to_terms(files: Vec<PathBuf>) -> (TermEnv, TypeEnv) {
    let lexer = isle::lexer::Lexer::from_files(files).unwrap();
    parse_isle_to_terms(lexer)
}

/// Produces the two ISLE-defined structs with type and term environments
fn parse_isle_to_terms(lexer: isle::lexer::Lexer) -> (TermEnv, TypeEnv) {
    // Parses to an AST, as a list of definitions
    let defs = isle::parser::parse(lexer).expect("should parse");

    // Produces maps from symbols/names to types
    let mut typeenv = TypeEnv::from_ast(&defs).unwrap();

    // Produces a list of terms, rules, and map from symbols to terms
    let termenv = TermEnv::from_ast(&mut typeenv, &defs).unwrap();
    (termenv, typeenv)
}

fn verify_rule_for_type(
    rule: &Rule,
    termenv: &TermEnv,
    typeenv: &TypeEnv,
    ty: VIRType,
) -> VerificationResult {
    // For now, starting types must be bitvectors
    assert!(ty.is_bv());
    let (mut assumption_ctx, lhs) = AssumptionContext::from_lhs(&rule.lhs, termenv, typeenv, ty);
    let rhs = assumption_ctx.interp_sema_expr(&rule.rhs, termenv, typeenv, ty);
    run_solver(assumption_ctx, lhs, rhs, ty)
}

fn pattern_term_name(pattern: Pattern, termenv: &TermEnv, typeenv: &TypeEnv) -> String {
    match pattern {
        Pattern::Term(_, termid, _) => {
            let term = &termenv.terms[termid.index()];
            typeenv.syms[term.name.index()].clone()
        }
        _ => unreachable!("Must be term"),
    }
}

fn verify_rules_with_lhs_root(root: &str, termenv: &TermEnv, typeenv: &TypeEnv) {
    for ty in all_starting_bitvectors() {
        for rule in &termenv.rules {
            if pattern_term_name(rule.lhs.clone(), termenv, typeenv) == root {
                let _res = verify_rule_for_type(rule, termenv, typeenv, ty);
            }
        }
    }
}

fn main() {
    let cur_dir = env::current_dir().expect("Can't access current working directory");

    // TODO: clean up path logic
    let clif_isle = cur_dir.join("../../../codegen/src").join("clif.isle");
    let prelude_isle = cur_dir.join("../../../codegen/src").join("prelude.isle");

    // Disable for now to not have to consider all rules
    // let aarch64_isle = cur_dir.join("../../../codegen/src/isa/aarch64").join("inst.isle");

    let matches = Command::new("Verification Engine for ISLE")
        .arg(
            Arg::new("INPUT")
                .help("Sets the input file")
                .required(true)
                .index(1),
        )
        .get_matches();
    let input = PathBuf::from(matches.value_of("INPUT").unwrap());

    let inputs = vec![clif_isle, prelude_isle, input];

    let (termenv, typeenv) = isle_files_to_terms(inputs);

    // For now, verify rules rooted in `lower`
    verify_rules_with_lhs_root("lower", &termenv, &typeenv)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_iadds() {
        let prelude = "
        ;; TYPES
    
        (type Inst (primitive Inst))
        (type Type (primitive Type))
        (type Value (primitive Value))
    
        (type Reg (primitive Reg))
        (type ValueRegs (primitive ValueRegs))
    
        ;; Imm12 bv12
        (type Imm12 (primitive Imm12))
    
        ;; EXTRACTORS
        (decl lower (Inst) ValueRegs)
    
        (decl has_type (Type Inst) Inst)
        (extern extractor has_type has_type)
    
        ;; (decl (a) b SMTType) (assert (= a b) (<= a 64)))
        ;; {((a : Type) b : Type) | a = b, a.ty.width <= 64}
        ;; (decl fits_in_64 (Type) Type)
        (decl fits_in_64 (Type) Type)
        (extern extractor fits_in_64 fits_in_64)
    
        (decl fits_in_32 (Type) Type)
        (extern extractor fits_in_32 fits_in_32)
    
        ;; (decl (a b) c bvX) (assert (= c (+ a b)))
        (decl iadd (Value Value) Inst)
        (extern extractor iadd iadd)
    
        (decl imm12_from_negated_value (Imm12) Value)
        (extern extractor imm12_from_negated_value imm12_from_negated_value)
    
        ;; CONSTRUCTORS
    
        (decl value_reg (Reg) ValueRegs)
        (extern constructor value_reg value_reg)
    
        (decl add (Type Reg Reg) Reg)
        (extern constructor add add)
    
        (decl put_in_reg (Value) Reg)
        (extern constructor put_in_reg put_in_reg)
    
        (decl sub_imm (Type Reg Imm12) Reg)
        (extern constructor sub_imm sub_imm)
        ";

        let simple_iadd = "(rule (lower (has_type (fits_in_64 ty) (iadd x y)))
            (value_reg (add ty (put_in_reg x) (put_in_reg y))))";

        let iadd_to_sub =
            "(rule (lower (has_type (fits_in_64 ty) (iadd x (imm12_from_negated_value y))))
            (value_reg (sub_imm ty (put_in_reg x) y)))";

        // Go through i1 to i128
        for ty in all_starting_bitvectors() {
            // The expected result is based on whether the type matches fits_in_64
            let expected_result = if ty.width() <= 64 {
                VerificationResult::Success
            } else {
                VerificationResult::InapplicableRule
            };
            {
                println!("{:-^1$}", format!("simple iadd bv{}", ty.width()), 80);
                println!("\nRunning verification for rule:\n{}\n", simple_iadd);
                let simple_iadd = prelude.to_owned() + simple_iadd;
                let (termenv, typeenv) = isle_str_to_terms(&simple_iadd);
                let res = verify_rule_for_type(&termenv.rules[0], &termenv, &typeenv, ty);
                assert_eq!(res, expected_result);
            }
            {
                println!("{:-^1$}", format!("iadd to sub bv{}", ty.width()), 80);
                println!("\nRunning verification for rule:\n{}\n", iadd_to_sub);
                let iadd_to_sub = prelude.to_owned() + iadd_to_sub;
                let (termenv, typeenv) = isle_str_to_terms(&iadd_to_sub);
                let res = verify_rule_for_type(&termenv.rules[0], &termenv, &typeenv, ty);
                assert_eq!(res, expected_result);
            }
        }
    }
    #[test]
    fn test_implicit_conversions() {
        let prelude = "
        ;; TYPES
    
        (type Inst (primitive Inst))
        (type Type (primitive Type))
        (type Value (primitive Value))
    
    
        (type Reg (primitive Reg))
        (type ValueRegs (primitive ValueRegs))
    
        ;; Imm12 bv12
        (type Imm12 (primitive Imm12))

        ;; NEW: IMPLICIT CONVERTERS
        (convert Reg ValueRegs value_reg)
        (convert Value Reg put_in_reg)
    
        ;; EXTRACTORS
        (decl lower (Inst) ValueRegs)
    
        (decl has_type (Type Inst) Inst)
        (extern extractor has_type has_type)
    
        ;; (decl (a) b SMTType) (assert (= a b) (<= a 64)))
        ;; {((a : Type) b : Type) | a = b, a.ty.width <= 64}
        ;; (decl fits_in_64 (Type) Type)
        (decl fits_in_64 (Type) Type)
        (extern extractor fits_in_64 fits_in_64)
    
        (decl fits_in_32 (Type) Type)
        (extern extractor fits_in_32 fits_in_32)
    
        ;; (decl (a b) c bvX) (assert (= c (+ a b)))
        (decl iadd (Value Value) Inst)
        (extern extractor iadd iadd)
    
        (decl imm12_from_negated_value (Imm12) Value)
        (extern extractor imm12_from_negated_value imm12_from_negated_value)
    
        ;; CONSTRUCTORS
    
        (decl add (Type Reg Reg) Reg)
        (extern constructor add add)
    
        (decl sub_imm (Type Reg Imm12) Reg)
        (extern constructor sub_imm sub_imm)

        (decl value_reg (Reg) ValueRegs)
        (extern constructor value_reg value_reg)
    
        (decl put_in_reg (Value) Reg)
        (extern constructor put_in_reg put_in_reg)
        ";

        let simple_iadd = "(rule (lower (has_type (fits_in_64 ty) (iadd x y)))
            (add ty x y))";

        let iadd_to_sub =
            "(rule (lower (has_type (fits_in_64 ty) (iadd x (imm12_from_negated_value y))))
            (sub_imm ty x y))";

        // Go through i1 to i128
        for ty in all_starting_bitvectors() {
            // The expected result is based on whether the type matches fits_in_64
            let expected_result = if ty.clone().width() <= 64 {
                VerificationResult::Success
            } else {
                VerificationResult::InapplicableRule
            };
            {
                println!("{:-^1$}", format!("simple iadd bv{}", ty.clone().width()), 80);
                println!("\nRunning verification for rule:\n{}\n", simple_iadd);
                let simple_iadd = prelude.to_owned() + simple_iadd;
                let (termenv, typeenv) = isle_str_to_terms(&simple_iadd);
                let res = verify_rule_for_type(&termenv.rules[0], &termenv, &typeenv, ty);
                assert_eq!(res, expected_result);
            }
            {
                println!("{:-^1$}", format!("iadd to sub bv{}", ty.width()), 80);
                println!("\nRunning verification for rule:\n{}\n", iadd_to_sub);
                let iadd_to_sub = prelude.to_owned() + iadd_to_sub;
                let (termenv, typeenv) = isle_str_to_terms(&iadd_to_sub);
                let res = verify_rule_for_type(&termenv.rules[0], &termenv, &typeenv, ty);
                assert_eq!(res, expected_result);
            }
        }
    }
}
