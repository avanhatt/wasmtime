// This file will be replaced by a parser that consumes annotations and produces
// the same type of structure, but for now, manually construct these annotations.

use veri_ir::{VIRType, BVExpr, BoundVar, VIRAnnotation, FunctionAnnotation, BoolExpr};
use std::cmp::Ordering;

pub fn isle_annotation_for_term(term: String, ty: VIRType) -> VIRAnnotation {
    match term.as_str() {
        "lower" => {
            // No-op for now
            let arg = BoundVar{ name: "arg".to_string(), ty};
            let result = BoundVar{ name: "ret".to_string(), ty};
            let identity = VIRType::bool_eq(arg.as_expr(), result.as_expr());
            let func = FunctionAnnotation{args: vec![arg], result};
            VIRAnnotation {
                func,
                assertions: vec![identity]
            }
        }
        "has_type" => {
            // No-op for now
            let ty_arg = BoundVar{ name: "ty".to_string(), ty};
            let arg = BoundVar{ name: "arg".to_string(), ty};
            let result = BoundVar{ name: "ret".to_string(), ty};
            let identity = VIRType::bool_eq(arg.as_expr(), result.as_expr());
            let func = FunctionAnnotation{args: vec![ty_arg, arg], result: result};
            VIRAnnotation {
                func,
                assertions: vec![identity]
            }
        }
        "fits_in_64" => {
            // Identity, but add assertion on type
            let arg = BoundVar{ name: "arg".to_string(), ty};
            let result = BoundVar{ name: "ret".to_string(), ty};
            let identity = VIRType::bool_eq(arg.as_expr(), result.as_expr());
            let ty_fits =  match ty {
                VIRType::BitVector(s) => {
                    if s <= 64 {
                        BoolExpr::True
                    } else {
                        BoolExpr::False
                    }
                }
                _ => unreachable!("{:?}", ty),
            };
            let func = FunctionAnnotation{args: vec![arg], result: result};
            VIRAnnotation {
                func,
                assertions: vec![identity, ty_fits]
            }
        }
        "imm12_from_negated_value" => {
            let bv12 = VIRType::BitVector(12);
            let imm_arg = BoundVar{ name: "imm_arg".to_string(), ty: bv12};
            let result = BoundVar{ name: "ret".to_string(), ty};
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
                Ordering::Greater => bv12.bv_extend(BVExpr::BVZeroExt, width_diff.try_into().unwrap(), imm_arg.as_expr()),
                Ordering::Equal => imm_arg.as_expr(),
            };
            let res = ty.bv_unary(BVExpr::BVNeg, as_ty);
            let res_assertion = VIRType::bool_eq(res, result.as_expr());
            let func = FunctionAnnotation{args: vec![imm_arg], result};
            VIRAnnotation {
                func,
                assertions: vec![assume_fits, res_assertion]
            }
        }
        "sub_imm" => {
            let bv12 = VIRType::BitVector(12);

            // Declare bound variables
            let ty_arg = BoundVar{ name: "ty".to_string(), ty: VIRType::IsleType};
            let reg_arg = BoundVar{ name: "reg".to_string(), ty};
            let imm_arg = BoundVar{ name: "imm_arg".to_string(), ty: bv12};
            let result = BoundVar{ name: "ret".to_string(), ty};

            let width_diff = (ty.width() as i128) - 12;
            let as_ty = match width_diff.cmp(&0) {
                Ordering::Less => bv12.bv_extract(0, ty.width() - 1, imm_arg.as_expr()),
                Ordering::Greater => bv12.bv_extend(BVExpr::BVZeroExt, width_diff.try_into().unwrap(), imm_arg.as_expr()),
                Ordering::Equal => imm_arg.as_expr()
            };
            let res = ty.bv_binary(
                BVExpr::BVSub,
                reg_arg.as_expr(),
                as_ty,
            );
            let assertion = VIRType::bool_eq(res, result.as_expr());
            let func = FunctionAnnotation{args: vec![ty_arg, reg_arg, imm_arg], result};
            VIRAnnotation {
                func,
                assertions: vec![assertion]
            }
        }
        _ => unimplemented!("Need annotation for term {}", term)
    }
}