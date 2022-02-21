// This file will be replaced by a parser that consumes annotations and produces
// the same type of structure, but for now, manually construct these annotations.

use std::cmp::Ordering;
use veri_ir::{BVExpr, BoolExpr, BoundVar, FunctionAnnotation, VIRAnnotation, VIRType};

fn rename_bv_expr<F>(e: BVExpr, rename: F) -> BVExpr
where
    F: Fn(&BoundVar) -> BoundVar + Copy,
{
    let f = |x: Box<BVExpr>| Box::new(rename_bv_expr(*x, rename));
    match e {
        BVExpr::Const(..) => e,
        BVExpr::Var(v) => BVExpr::Var(rename(&v)),
        BVExpr::BVNeg(ty, x) => BVExpr::BVNeg(ty, f(x)),
        BVExpr::BVNot(ty, x) => BVExpr::BVNot(ty, f(x)),
        BVExpr::BVAdd(ty, x, y) => BVExpr::BVAdd(ty, f(x), f(y)),
        BVExpr::BVSub(ty, x, y) => BVExpr::BVSub(ty, f(x), f(y)),
        BVExpr::BVAnd(ty, x, y) => BVExpr::BVAnd(ty, f(x), f(y)),
        BVExpr::BVZeroExt(ty, i, x) => BVExpr::BVZeroExt(ty, i, f(x)),
        BVExpr::BVSignExt(ty, i, x) => BVExpr::BVSignExt(ty, i, f(x)),
        BVExpr::BVExtract(ty, l, h, x) => BVExpr::BVExtract(ty, l, h, f(x)),
    }
}

fn rename_bool_expr<F>(e: BoolExpr, rename: F) -> BoolExpr
where
    F: Fn(&BoundVar) -> BoundVar + Copy,
{
    let f = |x: Box<BoolExpr>| Box::new(rename_bool_expr(*x, rename));
    match e {
        BoolExpr::True | BoolExpr::False => e,
        BoolExpr::Not(x) => BoolExpr::Not(f(x)),
        BoolExpr::And(x, y) => BoolExpr::And(f(x), f(y)),
        BoolExpr::Or(x, y) => BoolExpr::Or(f(x), f(y)),
        BoolExpr::Imp(x, y) => BoolExpr::Imp(f(x), f(y)),
        BoolExpr::Eq(x, y) => {
            VIRType::bool_eq(rename_bv_expr(*x, rename), rename_bv_expr(*y, rename))
        }
    }
}

pub fn rename_annotation_vars<F>(a: VIRAnnotation, rename: F) -> VIRAnnotation
where
    F: Fn(&BoundVar) -> BoundVar + Copy,
{
    let args = a.func.args.iter().map(rename).collect();
    let result = rename(&a.func.result);
    VIRAnnotation {
        func: veri_ir::FunctionAnnotation {
            args: args,
            result: a.func.result,
        },
        assertions: a.assertions,
    }
}

pub fn isle_annotation_for_term(term: &String, ty: VIRType) -> VIRAnnotation {
    match term.as_str() {
        "lower" => {
            // No-op for now
            let arg = BoundVar {
                name: "arg".to_string(),
                ty,
            };
            let result = BoundVar {
                name: "ret".to_string(),
                ty,
            };
            let identity = VIRType::bool_eq(arg.as_expr(), result.as_expr());
            let func = FunctionAnnotation {
                args: vec![arg],
                result,
            };
            VIRAnnotation {
                func,
                assertions: vec![identity],
            }
        }
        "has_type" => {
            // No-op for now
            let ty_arg = BoundVar {
                name: "ty".to_string(),
                ty,
            };
            let arg = BoundVar {
                name: "arg".to_string(),
                ty,
            };
            let result = BoundVar {
                name: "ret".to_string(),
                ty,
            };
            let identity = VIRType::bool_eq(arg.as_expr(), result.as_expr());
            let func = FunctionAnnotation {
                args: vec![ty_arg, arg],
                result: result,
            };
            VIRAnnotation {
                func,
                assertions: vec![identity],
            }
        }
        "fits_in_64" => {
            // Identity, but add assertion on type
            let arg = BoundVar {
                name: "arg".to_string(),
                ty,
            };
            let result = BoundVar {
                name: "ret".to_string(),
                ty,
            };
            let identity = VIRType::bool_eq(arg.as_expr(), result.as_expr());
            let ty_fits = match ty {
                VIRType::BitVector(s) => {
                    if s <= 64 {
                        BoolExpr::True
                    } else {
                        BoolExpr::False
                    }
                }
                _ => unreachable!("{:?}", ty),
            };
            let func = FunctionAnnotation {
                args: vec![arg],
                result: result,
            };
            VIRAnnotation {
                func,
                assertions: vec![identity, ty_fits],
            }
        }
        "iadd" => {
            let a = BoundVar {
                name: "a".to_string(),
                ty,
            };
            let b = BoundVar {
                name: "b".to_string(),
                ty,
            };
            let r = BoundVar {
                name: "r".to_string(),
                ty,
            };
            let sem = VIRType::bool_eq(
                ty.bv_binary(BVExpr::BVAdd, a.as_expr(), b.as_expr()),
                r.as_expr(),
            );
            let func = FunctionAnnotation {
                args: vec![a, b],
                result: r,
            };
            VIRAnnotation {
                func,
                assertions: vec![sem],
            }
        }
        // ((imm_arg : BV12) -> (ret: BV))
        "imm12_from_negated_value" => {
            let bv12 = VIRType::BitVector(12);
            let imm_arg = BoundVar {
                name: "imm_arg".to_string(),
                ty: bv12,
            };
            let result = BoundVar {
                name: "ret".to_string(),
                ty,
            };

            // *This* value's negated value fits in 12 bits
            let assume_fits = VIRType::bool_eq(
                ty.bv_binary(
                    BVExpr::BVAnd,
                    ty.bv_unary(BVExpr::BVNot, ty.bv_const(2_i128.pow(12) - 1)),
                    imm_arg.as_expr(),
                ),
                ty.bv_const(0),
            );
            let width_diff = (ty.width() as i128) - 12;
            let as_ty = match width_diff.cmp(&0) {
                Ordering::Less => bv12.bv_extract(0, ty.width() - 1, imm_arg.as_expr()),
                Ordering::Greater => bv12.bv_extend(
                    BVExpr::BVZeroExt,
                    width_diff.try_into().unwrap(),
                    imm_arg.as_expr(),
                ),
                Ordering::Equal => imm_arg.as_expr(),
            };
            let res = ty.bv_unary(BVExpr::BVNeg, as_ty);
            let res_assertion = VIRType::bool_eq(res, result.as_expr());
            let func = FunctionAnnotation {
                args: vec![imm_arg],
                result,
            };
            VIRAnnotation {
                func,
                assertions: vec![assume_fits, res_assertion],
            }
        }
        // TODO: wrapper for LHS vs RHS
        // TODO: helper for "convert bv type to another" with bv_extract
        "sub_imm" => {
            let bv12 = VIRType::BitVector(12);

            // Declare bound variables
            let ty_arg = BoundVar {
                name: "ty".to_string(),
                ty: VIRType::IsleType,
            };
            let reg_arg = BoundVar {
                name: "reg".to_string(),
                ty,
            };
            let imm_arg = BoundVar {
                name: "imm_arg".to_string(),
                ty: bv12,
            };
            let result = BoundVar {
                name: "ret".to_string(),
                ty,
            };

            let width_diff = (ty.width() as i128) - 12;
            let as_ty = match width_diff.cmp(&0) {
                Ordering::Less => bv12.bv_extract(0, ty.width() - 1, imm_arg.as_expr()),
                Ordering::Greater => bv12.bv_extend(
                    BVExpr::BVZeroExt,
                    width_diff.try_into().unwrap(),
                    imm_arg.as_expr(),
                ),
                Ordering::Equal => imm_arg.as_expr(),
            };
            let res = ty.bv_binary(BVExpr::BVSub, reg_arg.as_expr(), as_ty);
            let assertion = VIRType::bool_eq(res, result.as_expr());
            let func = FunctionAnnotation {
                args: vec![ty_arg, reg_arg, imm_arg],
                result,
            };
            VIRAnnotation {
                func,
                assertions: vec![assertion],
            }
        }
        _ => unimplemented!("Need annotation for term {}", term),
    }
}
