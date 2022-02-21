use cranelift_isle as isle;
use isle::sema::{Rule, TermEnv, TypeEnv};
use veri_ir::{all_starting_bitvectors, VIRType};

use crate::external_semantics::run_solver;
use crate::interp_lhs::AssumptionContext;
use crate::interp_rhs::InterpContext;

mod external_semantics;
mod interp_lhs;
mod interp_rhs;
mod isle_annotations;

// Produces the two ISLE-defined structs with type and term environments
fn parse_isle_to_terms(s: &str) -> (TermEnv, TypeEnv) {
    let lexer = isle::lexer::Lexer::from_str(s, "fuzz-input.isle").unwrap();

    // Parses to an AST, as a list of definitions
    let defs = isle::parser::parse(lexer).expect("should parse");

    // Produces maps from symbols/names to types
    let mut typeenv = TypeEnv::from_ast(&defs).unwrap();

    // Produces a list of terms, rules, and map from symbols to terms
    let termenv = TermEnv::from_ast(&mut typeenv, &defs).unwrap();
    (termenv, typeenv)
}

fn verification_conditions_for_rule(
    rule: &Rule,
    termenv: &TermEnv,
    typeenv: &TypeEnv,
    ty: VIRType,
) {
    let mut interp_ctx = InterpContext {};
    if let Some((assumption_ctx, lhs)) =
        AssumptionContext::from_lhs(&rule.lhs, termenv, typeenv, ty)
    {
        let rhs = interp_ctx.interp_rhs(&rule.rhs, &assumption_ctx, termenv, typeenv, ty);
        run_solver(assumption_ctx, lhs, rhs, ty);
    } else {
        println!("Skipping solver for inapplicable rule")
    }
}

// for simple iadd
// TYPE = 32

// ASSUMPTIONS
// (fits_in_64 ty) becomes [1] (decl-const ty 32 INT) [2] TRUE (<= 32 64)
// (iadd x y) becomes [1] (decl-const a BV32), (decl-const b BV32), [2] (= x a), (= y b)
// probably want an IR for our own type env that maps (a -> BV32)
// assumptions we might wanna keep as SMTLIB for now, later might want our own IR
// if Rust can easily tell you the assumption is false, bail

// LHS TERM
// see that iadd terminates our understanding, need to get it from somewhere
// see that
// [1]
// (decl-fun (has_type ty i) i)
// (decl-fun (iadd i j) (bvadd i j))
// [2]
// (has_type (fits_in_64 ty) (iadd x y))

// RHS TERM
// look up that in our interpreter context that we have defns for ty, x, y
// interpret term based on defs

// FINAL QUERY:
// !((let (boundvars ...) (assumptions => (= lhs rhs)))

// 3 options for what to do when we see add
// first, we could stop here and just annotate a defn for add
// OR, we can _keep going_ and split state for every rule with iadd on LHS
// OR, we can _keep going_ and for now, dynamically fail if more than one rule with iadd on the LHS meets our TYPE condition

// Other thoughts:
//  - separate queries per-type and per top-level rule. Eventually probably want cacheing system.
//  - will we eventually position this as a symbolic executer? Something more specific?

fn main() {
    let prelude = "
    ;; TYPES

    ;; Inst UF
    (type Inst (primitive Inst))

    ;; Type Int
    (type Type (primitive Type))

    ;; Value bvX
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
    ;; TODO: replace with more rules
    (extern extractor iadd iadd)

    (decl imm12_from_negated_value (Imm12) Value)
    (extern extractor imm12_from_negated_value imm12_from_negated_value)

    ;; CONSTRUCTORS

    (decl value_reg (Reg) ValueRegs)
    (extern constructor value_reg value_reg)

    (decl add (Type Reg Reg) Reg)
    ;; TODO: replace with more rules
    (extern constructor add add)

    (decl put_in_reg (Value) Reg)
    (extern constructor put_in_reg put_in_reg)

    (decl sub_imm (Type Reg Imm12) Reg)
    (extern constructor sub_imm sub_imm)
    ";

    // TODO: annotations are first priority

    let simple_iadd = "(rule (lower (has_type (fits_in_64 ty) (iadd x y)))
        (value_reg (add ty (put_in_reg x) (put_in_reg y))))";

    let iadd_to_sub =
        "(rule (lower (has_type (fits_in_64 ty) (iadd x (imm12_from_negated_value y))))
        (value_reg (sub_imm ty (put_in_reg x) y)))";

    // Go through i1 to i128
    for ty in all_starting_bitvectors() {
        {
            println!("{:-^1$}", format!("simple iadd bv{}", ty.width()), 80);
            println!("\nRunning verification for rule:\n{}\n", simple_iadd);
            let simple_iadd = prelude.to_owned() + simple_iadd;
            let (termenv, typeenv) = parse_isle_to_terms(&simple_iadd);
            verification_conditions_for_rule(&termenv.rules[0], &termenv, &typeenv, ty);
        }

        {
            println!("{:-^1$}", format!("iadd to sub bv{}", ty.width()), 80);
            println!("\nRunning verification for rule:\n{}\n", iadd_to_sub);
            let iadd_to_sub = prelude.to_owned() + iadd_to_sub;
            let (termenv, typeenv) = parse_isle_to_terms(&iadd_to_sub);
            verification_conditions_for_rule(&termenv.rules[0], &termenv, &typeenv, ty);
        }
    }
}

// Open questions 2022-02-07
// 1. Syntax for term semantics spec
// 2. Avoiding `has_type` special casing/final type
// isle approach: separate core lang from IL prelude
// 3. Rule depth/static inlining

// Re: 1: syntax ideas

// name =
// { (arg1, arg2, res1) | ... }
// u
// { (arg1, arg2, res2) | ... }
// (rule (name arg1 arg2)
//       (res1))
// (rule (name arg1 arg2)
//       (res2))
// ---
// imm12_from_negated_value =
//
// (simple idea)
// { (a, b) | b = extract(neg(a)) && fits(neg(a), 12) }
// { (a, b) | a = neg(zext(b)) }
//
// (in practice)
// { (a, b) | b = conv(neg(a)) && fits(neg(a), 12) }
// { (a, b) | a = neg(conv(b)) }
//
// where conv if defined as either extract or zext
// conv =
// { (x, y) | if x.ty - y.ty > 0 {...} else {...} }
//
//
// ---
// (rule (...)
//     (imm12_from_negated_value ...)
//     (m_rotl ...))

// Re: width of the register
// (decl sub_imm (Type Reg Imm12) Reg)
// (rule (sub_imm (fits_in_32 _ty) x y) (sub32_imm x y))
// (rule (sub_imm $I64 x y) (sub64_imm x y))

// (decl sub32_imm (Reg Imm12) Reg)
// (rule (sub32_imm x y) (alu_rr_imm12 (ALUOp.Sub32) x y))

// (decl sub64_imm (Reg Imm12) Reg)
// (rule (sub64_imm x y) (alu_rr_imm12 (ALUOp.Sub64) x y))
