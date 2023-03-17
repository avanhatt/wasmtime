use veri_ir::Type;

use std::collections::HashMap;

pub fn isle_inst_types() -> HashMap<&'static str, Vec<Vec<Type>>> {
    let bv_types_8_to_64: Vec<Type> = vec![
        Type::BitVector(Some(8)),
        Type::BitVector(Some(16)),
        Type::BitVector(Some(32)),
        Type::BitVector(Some(64)),
    ];

    let bv_unary_8_to_64: Vec<Vec<Type>> =
        bv_types_8_to_64.iter().copied().map(|x| vec![x]).collect();

    let bv_binary_8_to_64: Vec<Vec<Type>> = bv_types_8_to_64
        .iter()
        .copied()
        .map(|x| vec![x, x])
        .collect();

    let mut widths = HashMap::new();

    // Simple unary
    widths.insert("ineg", bv_unary_8_to_64.clone());
    widths.insert("cls", bv_unary_8_to_64.clone());
    widths.insert("clz", bv_unary_8_to_64.clone());
    widths.insert("ctz", bv_unary_8_to_64.clone());

    // Unary with variable return width
    widths.insert("sextend", bv_unary_8_to_64.clone());
    widths.insert("uextend", bv_unary_8_to_64.clone());

    // Binary
    widths.insert("iadd", bv_binary_8_to_64.clone());
    widths.insert("isub", bv_binary_8_to_64.clone());
    widths.insert("imul", bv_binary_8_to_64.clone());
    widths.insert("band", bv_binary_8_to_64.clone());
    widths.insert("bor", bv_binary_8_to_64.clone());
    widths.insert("bxor", bv_binary_8_to_64.clone());
    widths.insert("ushr", bv_binary_8_to_64.clone());
    widths.insert("sshr", bv_binary_8_to_64.clone());
    widths.insert("ishl", bv_binary_8_to_64.clone());

    // Binary with possibly differing widths
    widths.insert("rotl", bv_binary_8_to_64.clone());
    widths.insert("rotr", bv_binary_8_to_64.clone());

    // Intermediate terms
    // (decl small_rotr (Type Reg Reg) Reg)
    widths.insert(
        "small_rotr",
        vec![vec![
            Type::Int,
            Type::BitVector(Some(64)),
            Type::BitVector(Some(64)),
        ]],
    );

    // (decl small_rotr_imm (Type Reg ImmShift) Reg)
    widths.insert(
        "small_rotr_imm",
        vec![vec![
            Type::Int,
            Type::BitVector(Some(6)),
            Type::BitVector(Some(64)),
        ]],
    );

    // (decl do_shift (ALUOp Type Reg Value) Reg)
    widths.insert(
        "do_shift",
        vec![
            vec![
                Type::Int,
                Type::Int,
                Type::BitVector(Some(64)),
                Type::BitVector(Some(8)),
            ],
            vec![
                Type::Int,
                Type::Int,
                Type::BitVector(Some(64)),
                Type::BitVector(Some(16)),
            ],
            vec![
                Type::Int,
                Type::Int,
                Type::BitVector(Some(64)),
                Type::BitVector(Some(32)),
            ],
            vec![
                Type::Int,
                Type::Int,
                Type::BitVector(Some(64)),
                Type::BitVector(Some(64)),
            ],
        ],
    );

    return widths;
}
