use crate::annotations::AnnotationEnv;
use cranelift_isle::sema::{TermEnv, TypeEnv};
use std::{collections::HashMap, vec};
use veri_ir::{TermSignature, Type};

pub fn isle_inst_types(
    termenv: &TermEnv,
    typeenv: &TypeEnv,
    annotation_env: &AnnotationEnv,
) -> HashMap<String, Vec<TermSignature>> {
    let mut inst_types = HashMap::new();

    // Populate from ISLE.
    for (term_id, term_sigs) in &annotation_env.instantiations_map {
        let sym = termenv.terms[term_id.index()].name;
        let name = typeenv.syms[sym.index()].clone();
        inst_types.insert(name, term_sigs.clone());
    }

    // Apply overrides.
    let overrides = isle_inst_types_overrides();
    for (name, term_sigs) in &overrides {
        let name = name.to_string();
        if let Some(exist) = inst_types.get(&name) {
            assert_eq!(exist, term_sigs);
        }
        inst_types.insert(name, term_sigs.clone());
    }

    inst_types
}

fn isle_inst_types_overrides() -> HashMap<&'static str, Vec<TermSignature>> {
    let mut widths = HashMap::new();

    // Intermediate terms

    // (decl small_rotr_imm (Type Reg ImmShift) Reg)
    widths.insert(
        "small_rotr_imm",
        vec![TermSignature {
            args: vec![
                Type::Int,
                Type::BitVector(Some(64)),
                Type::BitVector(Some(6)),
            ],
            ret: Type::BitVector(Some(64)),
            canonical_type: Some(Type::BitVector(Some(64))),
        }],
    );

    // (decl do_shift (ALUOp Type Reg Value) Reg)
    widths.insert(
        "do_shift",
        vec![
            TermSignature {
                args: vec![
                    Type::BitVector(Some(8)),
                    Type::Int,
                    Type::BitVector(Some(64)),
                    Type::BitVector(Some(8)),
                ],
                ret: Type::BitVector(Some(64)),
                canonical_type: Some(Type::BitVector(Some(8))),
            },
            TermSignature {
                args: vec![
                    Type::BitVector(Some(8)),
                    Type::Int,
                    Type::BitVector(Some(64)),
                    Type::BitVector(Some(16)),
                ],
                ret: Type::BitVector(Some(64)),
                canonical_type: Some(Type::BitVector(Some(16))),
            },
            TermSignature {
                args: vec![
                    Type::BitVector(Some(8)),
                    Type::Int,
                    Type::BitVector(Some(64)),
                    Type::BitVector(Some(32)),
                ],
                ret: Type::BitVector(Some(64)),
                canonical_type: Some(Type::BitVector(Some(32))),
            },
            TermSignature {
                args: vec![
                    Type::BitVector(Some(8)),
                    Type::Int,
                    Type::BitVector(Some(64)),
                    Type::BitVector(Some(64)),
                ],
                ret: Type::BitVector(Some(64)),
                canonical_type: Some(Type::BitVector(Some(64))),
            },
        ],
    );

    //  (decl pure imm12_from_negated_value (Value) Imm12)
    widths.insert(
        "imm12_from_negated_value",
        vec![
            TermSignature {
                args: vec![Type::BitVector(Some(8))],
                ret: Type::BitVector(Some(24)),
                canonical_type: Some(Type::BitVector(Some(8))),
            },
            TermSignature {
                args: vec![Type::BitVector(Some(16))],
                ret: Type::BitVector(Some(24)),
                canonical_type: Some(Type::BitVector(Some(16))),
            },
            TermSignature {
                args: vec![Type::BitVector(Some(32))],
                ret: Type::BitVector(Some(24)),
                canonical_type: Some(Type::BitVector(Some(32))),
            },
            TermSignature {
                args: vec![Type::BitVector(Some(64))],
                ret: Type::BitVector(Some(24)),
                canonical_type: Some(Type::BitVector(Some(64))),
            },
        ],
    );

    widths.insert(
        "simplify",
        vec![
            TermSignature {
                args: vec![Type::BitVector(Some(8))],
                ret: Type::BitVector(Some(8)),
                canonical_type: Some(Type::BitVector(Some(8))),
            },
            TermSignature {
                args: vec![Type::BitVector(Some(16))],
                ret: Type::BitVector(Some(16)),
                canonical_type: Some(Type::BitVector(Some(16))),
            },
            TermSignature {
                args: vec![Type::BitVector(Some(32))],
                ret: Type::BitVector(Some(32)),
                canonical_type: Some(Type::BitVector(Some(32))),
            },
            TermSignature {
                args: vec![Type::BitVector(Some(64))],
                ret: Type::BitVector(Some(64)),
                canonical_type: Some(Type::BitVector(Some(64))),
            },
        ],
    );

    // ------------------------------------------
    // dump ISLE syntax
    println!("WIDTHS -------------------------------");
    for (name, sigs) in &widths {
        println!("(instantiate {name}");
        for sig in sigs {
            print!("    (");
            print!("(args");
            for arg in &sig.args {
                print!(" {}", type_to_string(&arg));
            }
            print!(")");
            print!(" (ret {})", type_to_string(&sig.ret));
            print!(" (canon {})", type_to_string(&sig.canonical_type.unwrap()));
            println!(")");
        }
        println!(")");
    }
    println!("WIDTHS -------------------------------");

    // // ------------------------------------------

    return widths;
}

fn type_to_string(ty: &Type) -> String {
    match ty {
        Type::BitVector(Some(width)) => format!("(bv {width})"),
        Type::BitVector(None) => "(bv)".to_string(),
        Type::Bool => "Bool".to_string(),
        Type::Int => "Int".to_string(),
    }
}
