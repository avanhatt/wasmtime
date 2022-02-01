use cranelift_isle as isle;
use isle::sema::{Rule, TermEnv, TypeEnv};
use types::SMTType;

use crate::assumptions::AssumptionContext;
use crate::external_semantics::run_solver;
use crate::interp::InterpContext;

mod assumptions;
mod external_semantics;
mod interp;
mod smt_ast;
mod types;

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
    ty: SMTType,
) {
    let mut interp_ctx = InterpContext {};
    let assumption_ctx = AssumptionContext::from_lhs(&rule.lhs, termenv, typeenv, ty);
    let lhs = interp_ctx.interp_lhs(&rule.lhs, &assumption_ctx, termenv, typeenv, ty);
    let rhs = interp_ctx.interp_rhs(&rule.rhs, &assumption_ctx, termenv, typeenv, ty);

    // dbg!(lhs);
    // dbg!(rhs);

    run_solver(assumption_ctx, lhs, rhs, ty);
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

    (type Inst (primitive Inst))
    (type Type (primitive Type))
    (type Value (primitive Value))
    (type Reg (primitive Reg))
    (type ValueRegs (primitive ValueRegs))

    ;; EXTRACTORS

    (decl lower (Inst) ValueRegs)

    (decl has_type (Type Inst) Inst)
    (extern extractor has_type has_type)

    (decl fits_in_64 (Type) Type)
    (extern extractor fits_in_64 fits_in_64)

    (decl iadd (Value Value) Inst)
    ;; TODO: replace with more rules
    (extern extractor iadd iadd)

    ;; CONSTRUCTORS

    (decl value_reg (Reg) ValueRegs)
    (extern constructor value_reg value_reg)

    (decl add (Type Reg Reg) Reg)
    ;; TODO: replace with more rules
    (extern constructor add add)

    (decl put_in_reg (Value) Reg)
    (extern constructor put_in_reg put_in_reg)
    ";

    let simple_iadd = prelude.to_owned()
        + "
    (rule (lower (has_type (fits_in_64 ty) (iadd x y)))
        (value_reg (add ty (put_in_reg x) (put_in_reg y))))";

    let iadd_to_sub = prelude.to_owned()
        + "
    (rule (lower (has_type (fits_in_64 ty) (iadd x (imm12_from_negated_value y))))
        (value_reg (sub_imm ty (put_in_reg x) y)))

    ";

    // For now, just a small specific type
    let ty = SMTType::BitVector(8);

    let (termenv, typeenv) = parse_isle_to_terms(&simple_iadd);
    verification_conditions_for_rule(&termenv.rules[0], &termenv, &typeenv, ty);
}
