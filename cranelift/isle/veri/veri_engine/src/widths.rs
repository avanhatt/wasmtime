use veri_ir::{Expr, Type};

use std::collections::HashMap;

pub fn only_width_logic(e: Expr) -> bool {
    match e {
        Expr::Terminal(_) => todo!(),
        Expr::Unary(_, _) => todo!(),
        Expr::Binary(_, _, _) => todo!(),
        Expr::CLZ(_) => todo!(),
        Expr::A64CLZ(_, _) => todo!(),
        Expr::CLS(_) => todo!(),
        Expr::A64CLS(_, _) => todo!(),
        Expr::Rev(_) => todo!(),
        Expr::A64Rev(_, _) => todo!(),
        Expr::Conditional(_, _, _) => todo!(),
        Expr::BVExtract(_, _, _) => todo!(),
        Expr::BVIntToBV(_, _) => todo!(),
        Expr::BVToInt(_) => todo!(),
        Expr::BVZeroExtTo(_, _) => todo!(),
        Expr::BVZeroExtToVarWidth(_, _) => todo!(),
        Expr::BVSignExtTo(_, _) => todo!(),
        Expr::BVSignExtToVarWidth(_, _) => todo!(),
        Expr::BVConvTo(_) => todo!(),
        Expr::BVConvToVarWidth(_, _) => todo!(),
        Expr::WidthOf(_) => todo!(),
        Expr::UndefinedTerm(_) => todo!(),
    }
}

pub fn isle_inst_types() -> HashMap<&'static str, Vec<Vec<Type>>> {
    let bv_types_8_to_64: Vec<Type> = vec![
        Type::BitVector(Some(8)),
        Type::BitVector(Some(16)),
        Type::BitVector(Some(32)),
        Type::BitVector(Some(64)),
    ];

    let bv_unary_8_to_65: Vec<Vec<Type>> = bv_types_8_to_64
        .iter()
        .copied()
        .map(|x| vec![x.clone()])
        .collect();

    let bv_binary_8_to_65: Vec<Vec<Type>> = bv_types_8_to_64
        .iter()
        .copied()
        .map(|x| vec![x.clone(), x.clone()])
        .collect();

    let mut widths = HashMap::new();

    // Simple unary
    widths.insert("ineg", bv_unary_8_to_65.clone());
    widths.insert("cls", bv_unary_8_to_65.clone());
    widths.insert("clz", bv_unary_8_to_65.clone());
    widths.insert("ctz", bv_unary_8_to_65.clone());

    // Unary with variable return width
    widths.insert("sextend", bv_unary_8_to_65.clone());
    widths.insert("uextend", bv_unary_8_to_65.clone());

    // Binary
    widths.insert("iadd", bv_binary_8_to_65.clone());
    widths.insert("isub", bv_binary_8_to_65.clone());
    widths.insert("imul", bv_binary_8_to_65.clone());
    widths.insert("band", bv_binary_8_to_65.clone());
    widths.insert("bor", bv_binary_8_to_65.clone());
    widths.insert("bxor", bv_binary_8_to_65.clone());

    // Binary with possibly differing widths
    widths.insert("rotl", bv_binary_8_to_65.clone());
    widths.insert("rotr", bv_binary_8_to_65.clone());

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

    return widths;
}
