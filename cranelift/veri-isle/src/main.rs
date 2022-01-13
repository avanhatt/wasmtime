
use cranelift_isle as isle;

// Conceptually returns: the list of definitions, plus a map symbol name -> type
fn lex_and_parse_isle(s: &str) {
    let lexer = isle::lexer::Lexer::from_str(s, "fuzz-input.isle");
    let lexer = match lexer {
        Ok(l) => l,
        Err(_) => return,
    };

    let defs = isle::parser::parse(lexer);
    dbg!(&defs);
    let defs = match defs {
        Ok(d) => d,
        Err(_) => return,
    };

    // Note: instead of compiling, just get type env

    let code = isle::compile::compile(&defs);
    dbg!(&code);
    let code = match code {
        Ok(c) => c,
        Err(_) => return,
    };
}

// trying to say from (lower (... (iadd (a) (b)))), make fresh vars a b of size TYPE
fn extract_quantified_terms_from_lhs() {

}
// maybe combined with above
// takes in LHS definitions, ty map, produces SMTLIB list (and together)
fn produce_assumptions_from_lhs() {
    ()
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



// 3 options for what to do when we see add
// first, we could stop here and just annotate a defn for add
// OR, we can _keep going_ and split state for every rule with iadd on LHS
// OR, we can _keep going_ and for now, dynamically fail if more than one rule with iadd on the LHS meets our TYPE condition

// Other thoughts: 
//  - seperate queries per-type and per top-level rule. Eventually probably want cacheing system. 
//  - will we eventually position this as a symbolic executer? Something more specific? 


fn main() {
    let simple_iadd = "
    (rule (lower (has_type (fits_in_64 ty) (iadd x y)))
        (value_reg (add ty (put_in_reg x) (put_in_reg y))))";

    let iadd_to_sub = 
    "
    (type Inst (primitive Inst))
    (type Type (primitive Type))
    (type Value (primitive Value))
    (type ValueRegs (primitive ValueRegs))
    (decl lower (Inst) ValueRegs)
    (decl has_type (Type Inst) Inst)

    (rule (lower (has_type (fits_in_64 ty) (iadd x (imm12_from_negated_value y))))
        (value_reg (sub_imm ty (put_in_reg x) y)))

    ";


    lex_and_parse_isle(simple_iadd);
}
