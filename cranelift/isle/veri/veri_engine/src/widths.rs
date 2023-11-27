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
    let bv_types_8_to_64: Vec<Type> = vec![
        Type::BitVector(Some(8)),
        Type::BitVector(Some(16)),
        Type::BitVector(Some(32)),
        Type::BitVector(Some(64)),
    ];

    let mut widths = HashMap::new();

    widths.insert(
        "operand_size",
        bv_types_8_to_64
            .iter()
            .copied()
            .map(|t| TermSignature {
                args: vec![Type::Int],
                ret: Type::Int,
                canonical_type: Some(t),
            })
            .collect(),
    );

    // (decl output_reg (Reg) InstOutput)
    widths.insert(
        "output_reg",
        bv_types_8_to_64
            .iter()
            .copied()
            .map(|t| TermSignature {
                args: vec![Type::BitVector(Some(64))],
                ret: t.clone(),
                canonical_type: Some(t),
            })
            .collect(),
    );

    // (decl imm (Type u64) Reg)
    widths.insert(
        "imm",
        bv_types_8_to_64
            .iter()
            .copied()
            .map(|t| TermSignature {
                args: vec![Type::Int, Type::BitVector(Some(64))],
                ret: Type::BitVector(Some(64)),
                canonical_type: Some(t.clone()),
            })
            .collect(),
    );

    // Unary with variable return width
    let extends = vec![
        TermSignature {
            args: vec![Type::BitVector(Some(8))],
            ret: Type::BitVector(Some(8)),
            canonical_type: Some(Type::BitVector(Some(8))),
        },
        TermSignature {
            args: vec![Type::BitVector(Some(8))],
            ret: Type::BitVector(Some(16)),
            canonical_type: Some(Type::BitVector(Some(8))),
        },
        TermSignature {
            args: vec![Type::BitVector(Some(8))],
            ret: Type::BitVector(Some(32)),
            canonical_type: Some(Type::BitVector(Some(8))),
        },
        TermSignature {
            args: vec![Type::BitVector(Some(8))],
            ret: Type::BitVector(Some(64)),
            canonical_type: Some(Type::BitVector(Some(8))),
        },
        TermSignature {
            args: vec![Type::BitVector(Some(16))],
            ret: Type::BitVector(Some(16)),
            canonical_type: Some(Type::BitVector(Some(16))),
        },
        TermSignature {
            args: vec![Type::BitVector(Some(16))],
            ret: Type::BitVector(Some(32)),
            canonical_type: Some(Type::BitVector(Some(16))),
        },
        TermSignature {
            args: vec![Type::BitVector(Some(16))],
            ret: Type::BitVector(Some(64)),
            canonical_type: Some(Type::BitVector(Some(16))),
        },
        TermSignature {
            args: vec![Type::BitVector(Some(32))],
            ret: Type::BitVector(Some(32)),
            canonical_type: Some(Type::BitVector(Some(32))),
        },
        TermSignature {
            args: vec![Type::BitVector(Some(32))],
            ret: Type::BitVector(Some(64)),
            canonical_type: Some(Type::BitVector(Some(32))),
        },
        TermSignature {
            args: vec![Type::BitVector(Some(64))],
            ret: Type::BitVector(Some(64)),
            canonical_type: Some(Type::BitVector(Some(64))),
        },
    ];
    widths.insert("sextend", extends.clone());
    widths.insert("uextend", extends.clone());

    // x86 binary
    widths.insert(
        "amode_add",
        vec![
            TermSignature {
                args: vec![Type::BitVector(Some(64)), Type::BitVector(Some(32))],
                ret: Type::BitVector(Some(64)),
                canonical_type: Some(Type::BitVector(Some(32))),
            },
            TermSignature {
                args: vec![Type::BitVector(Some(64)), Type::BitVector(Some(64))],
                ret: Type::BitVector(Some(64)),
                canonical_type: Some(Type::BitVector(Some(64))),
            },
        ],
    );

    // (decl to_amode_add (MemFlags Value Value Offset32) Amode)
    widths.insert(
        "to_amode_add",
        vec![TermSignature {
            args: vec![
                Type::BitVector(Some(8)),
                Type::BitVector(Some(64)),
                Type::BitVector(Some(64)),
                Type::BitVector(Some(32)),
            ],
            ret: Type::BitVector(Some(64)),
            canonical_type: Some(Type::BitVector(Some(64))),
        }],
    );

    // (decl amode_imm_reg (MemFlags Value Offset32) Amode)
    widths.insert(
        "amode_imm_reg",
        vec![TermSignature {
            args: vec![
                Type::BitVector(Some(8)),
                Type::BitVector(Some(64)),
                Type::BitVector(Some(32)),
            ],
            ret: Type::BitVector(Some(64)),
            canonical_type: Some(Type::BitVector(Some(64))),
        }],
    );

    // (decl amode_imm_reg_reg_shift (MemFlags Value Value Offset32) Amode)
    widths.insert(
        "amode_imm_reg_reg_shift",
        vec![TermSignature {
            args: vec![
                Type::BitVector(Some(8)),
                Type::BitVector(Some(64)),
                Type::BitVector(Some(64)),
                Type::BitVector(Some(32)),
            ],
            ret: Type::BitVector(Some(64)),
            canonical_type: Some(Type::BitVector(Some(64))),
        }],
    );

    widths.insert(
        "iconst",
        vec![
            TermSignature {
                args: vec![Type::BitVector(Some(64))],
                ret: Type::BitVector(Some(8)),
                canonical_type: Some(Type::BitVector(Some(8))),
            },
            TermSignature {
                args: vec![Type::BitVector(Some(64))],
                ret: Type::BitVector(Some(16)),
                canonical_type: Some(Type::BitVector(Some(16))),
            },
            TermSignature {
                args: vec![Type::BitVector(Some(64))],
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

    widths.insert(
        "null",
        vec![
            TermSignature {
                args: vec![],
                ret: Type::BitVector(Some(8)),
                canonical_type: Some(Type::BitVector(Some(8))),
            },
            TermSignature {
                args: vec![],
                ret: Type::BitVector(Some(16)),
                canonical_type: Some(Type::BitVector(Some(16))),
            },
            TermSignature {
                args: vec![],
                ret: Type::BitVector(Some(32)),
                canonical_type: Some(Type::BitVector(Some(32))),
            },
            TermSignature {
                args: vec![],
                ret: Type::BitVector(Some(64)),
                canonical_type: Some(Type::BitVector(Some(64))),
            },
        ],
    );

    widths.insert(
        "icmp",
        vec![
            TermSignature {
                args: vec![
                    Type::BitVector(Some(8)),
                    Type::BitVector(Some(8)),
                    Type::BitVector(Some(8)),
                ],
                ret: Type::BitVector(Some(8)),
                canonical_type: Some(Type::BitVector(Some(8))),
            },
            TermSignature {
                args: vec![
                    Type::BitVector(Some(8)),
                    Type::BitVector(Some(16)),
                    Type::BitVector(Some(16)),
                ],
                ret: Type::BitVector(Some(8)),
                canonical_type: Some(Type::BitVector(Some(16))),
            },
            TermSignature {
                args: vec![
                    Type::BitVector(Some(8)),
                    Type::BitVector(Some(32)),
                    Type::BitVector(Some(32)),
                ],
                ret: Type::BitVector(Some(8)),
                canonical_type: Some(Type::BitVector(Some(32))),
            },
            TermSignature {
                args: vec![
                    Type::BitVector(Some(8)),
                    Type::BitVector(Some(64)),
                    Type::BitVector(Some(64)),
                ],
                ret: Type::BitVector(Some(8)),
                canonical_type: Some(Type::BitVector(Some(64))),
            },
        ],
    );

    widths.insert(
        "lower_icmp_into_reg",
        vec![
            TermSignature {
                args: vec![
                    Type::BitVector(Some(8)),
                    Type::BitVector(Some(8)),
                    Type::BitVector(Some(8)),
                    Type::Int,
                    Type::Int,
                ],
                ret: Type::BitVector(Some(8)),
                canonical_type: Some(Type::BitVector(Some(8))),
            },
            TermSignature {
                args: vec![
                    Type::BitVector(Some(8)),
                    Type::BitVector(Some(16)),
                    Type::BitVector(Some(16)),
                    Type::Int,
                    Type::Int,
                ],
                ret: Type::BitVector(Some(8)),
                canonical_type: Some(Type::BitVector(Some(16))),
            },
            TermSignature {
                args: vec![
                    Type::BitVector(Some(8)),
                    Type::BitVector(Some(32)),
                    Type::BitVector(Some(32)),
                    Type::Int,
                    Type::Int,
                ],
                ret: Type::BitVector(Some(8)),
                canonical_type: Some(Type::BitVector(Some(32))),
            },
            TermSignature {
                args: vec![
                    Type::BitVector(Some(8)),
                    Type::BitVector(Some(64)),
                    Type::BitVector(Some(64)),
                    Type::Int,
                    Type::Int,
                ],
                ret: Type::BitVector(Some(8)),
                canonical_type: Some(Type::BitVector(Some(64))),
            },
        ],
    );

    widths.insert(
        "lower_icmp",
        vec![
            TermSignature {
                args: vec![
                    Type::BitVector(Some(8)),
                    Type::BitVector(Some(8)),
                    Type::BitVector(Some(8)),
                    Type::Int,
                ],
                ret: Type::BitVector(Some(12)),
                canonical_type: Some(Type::BitVector(Some(8))),
            },
            TermSignature {
                args: vec![
                    Type::BitVector(Some(8)),
                    Type::BitVector(Some(16)),
                    Type::BitVector(Some(16)),
                    Type::Int,
                ],
                ret: Type::BitVector(Some(12)),
                canonical_type: Some(Type::BitVector(Some(16))),
            },
            TermSignature {
                args: vec![
                    Type::BitVector(Some(8)),
                    Type::BitVector(Some(32)),
                    Type::BitVector(Some(32)),
                    Type::Int,
                ],
                ret: Type::BitVector(Some(12)),
                canonical_type: Some(Type::BitVector(Some(32))),
            },
            TermSignature {
                args: vec![
                    Type::BitVector(Some(8)),
                    Type::BitVector(Some(64)),
                    Type::BitVector(Some(64)),
                    Type::Int,
                ],
                ret: Type::BitVector(Some(12)),
                canonical_type: Some(Type::BitVector(Some(64))),
            },
        ],
    );

    // (decl lower_icmp_const (IntCC Value u64 Type) FlagsAndCC)
    widths.insert(
        "lower_icmp_const",
        vec![
            TermSignature {
                args: vec![
                    Type::BitVector(Some(8)),
                    Type::BitVector(Some(8)),
                    Type::BitVector(Some(64)),
                    Type::Int,
                ],
                ret: Type::BitVector(Some(12)),
                canonical_type: Some(Type::BitVector(Some(8))),
            },
            TermSignature {
                args: vec![
                    Type::BitVector(Some(8)),
                    Type::BitVector(Some(16)),
                    Type::BitVector(Some(64)),
                    Type::Int,
                ],
                ret: Type::BitVector(Some(12)),
                canonical_type: Some(Type::BitVector(Some(16))),
            },
            TermSignature {
                args: vec![
                    Type::BitVector(Some(8)),
                    Type::BitVector(Some(32)),
                    Type::BitVector(Some(64)),
                    Type::Int,
                ],
                ret: Type::BitVector(Some(12)),
                canonical_type: Some(Type::BitVector(Some(32))),
            },
            TermSignature {
                args: vec![
                    Type::BitVector(Some(8)),
                    Type::BitVector(Some(64)),
                    Type::BitVector(Some(64)),
                    Type::Int,
                ],
                ret: Type::BitVector(Some(12)),
                canonical_type: Some(Type::BitVector(Some(64))),
            },
        ],
    );

    // Intermediate terms
    // (decl small_rotr (Type Reg Reg) Reg)
    widths.insert(
        "small_rotr",
        vec![TermSignature {
            args: vec![
                Type::Int,
                Type::BitVector(Some(64)),
                Type::BitVector(Some(64)),
            ],
            ret: Type::BitVector(Some(64)),
            canonical_type: Some(Type::BitVector(Some(64))),
        }],
    );

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

    // ------------------------------------------

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
