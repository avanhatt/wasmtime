/// This file will be replaced by a parser that consumes annotations and produces
/// the same type of structure, but for now, manually construct these annotations.
use std::cmp::Ordering;
use veri_ir::{BoundVar, FunctionAnnotation, VIRAnnotation, VIRExpr, VIRType};

pub fn isle_annotation_for_term(term: &str, ty: VIRType) -> VIRAnnotation {
    match term {
        "lower" | "put_in_reg" | "value_reg" => {
            // No-op for now
            let arg = BoundVar {
                name: "arg".to_string(),
                ty,
            };
            let result = BoundVar {
                name: "ret".to_string(),
                ty,
            };
            let identity = VIRType::eq(arg.as_expr(), result.as_expr());
            let func = FunctionAnnotation {
                args: vec![arg],
                ret: result,
            };
            VIRAnnotation::new(
                func,
                vec![identity],
            )
        }
        "has_type" => {
            // Add an assertion on the type
            let ty_arg = BoundVar {
                name: "ty".to_string(),
                ty: VIRType::IsleType,
            };
            let arg = BoundVar {
                name: "arg".to_string(),
                ty,
            };
            let result = BoundVar {
                name: "ret".to_string(),
                ty,
            };
            let ty_eq = VIRType::eq(
                ty_arg.as_expr(),
                VIRType::IsleType.isle_type_const(ty.width() as i128),
            );
            let identity = VIRType::eq(arg.as_expr(), result.as_expr());
            let func = FunctionAnnotation {
                args: vec![ty_arg, arg],
                ret: result,
            };
            VIRAnnotation::new(
                func,
                vec![ty_eq, identity],
            )
        }
        "fits_in_64" => {
            // Identity, but add assertion on type
            dbg!(&ty);
            let arg = BoundVar {
                name: "arg".to_string(),
                ty,
            };
            let result = BoundVar {
                name: "ret".to_string(),
                ty,
            };
            let identity = VIRType::eq(arg.as_expr(), result.as_expr());
            let ty_fits = VIRType::lte(arg.as_expr(), VIRType::IsleType.isle_type_const(64_i128));
            let func = FunctionAnnotation {
                args: vec![arg],
                ret: result,
            };
            VIRAnnotation::new(
                func,
                vec![identity, ty_fits],
            )
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
            let sem = VIRType::eq(
                ty.bv_binary(VIRExpr::BVAdd, a.as_expr(), b.as_expr()),
                r.as_expr(),
            );
            let func = FunctionAnnotation {
                args: vec![a, b],
                ret: r,
            };
            VIRAnnotation::new(
                func,
                vec![sem],
            )
        }
        "add" => {
            let t = BoundVar {
                name: "ty".to_string(),
                ty: VIRType::IsleType,
            };
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
            let sem = VIRType::eq(
                ty.bv_binary(VIRExpr::BVAdd, a.as_expr(), b.as_expr()),
                r.as_expr(),
            );
            let func = FunctionAnnotation {
                args: vec![t, a, b],
                ret: r,
            };
            VIRAnnotation::new(
                func,
                vec![sem],
            )
        }
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

            // TODO: sanity check if we can remove this because of the following zext
            // *This* value's negated value fits in 12 bits
            let assume_fits = VIRType::eq(
                ty.bv_binary(
                    VIRExpr::BVAnd,
                    ty.bv_unary(VIRExpr::BVNot, ty.bv_const(2_i128.pow(12) - 1)),
                    result.as_expr(),
                ),
                ty.bv_const(0),
            );
            let width_diff = (ty.width() as i128) - 12;
            let as_ty = match width_diff.cmp(&0) {
                Ordering::Less => bv12.bv_extract(0, ty.width() - 1, imm_arg.as_expr()),
                Ordering::Greater => bv12.bv_extend(
                    VIRExpr::BVZeroExt,
                    width_diff.try_into().unwrap(),
                    imm_arg.as_expr(),
                ),
                Ordering::Equal => imm_arg.as_expr(),
            };
            let res = ty.bv_unary(VIRExpr::BVNeg, as_ty);
            let res_assertion = VIRType::eq(res, result.as_expr());
            let func = FunctionAnnotation {
                args: vec![imm_arg],
                ret: result,
            };
            VIRAnnotation::new(
                func,
                vec![assume_fits, res_assertion],
            )
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
                    VIRExpr::BVZeroExt,
                    width_diff.try_into().unwrap(),
                    imm_arg.as_expr(),
                ),
                Ordering::Equal => imm_arg.as_expr(),
            };
            let res = ty.bv_binary(VIRExpr::BVSub, reg_arg.as_expr(), as_ty);
            let assertion = VIRType::eq(res, result.as_expr());
            let func = FunctionAnnotation {
                args: vec![ty_arg, reg_arg, imm_arg],
                ret: result,
            };
            VIRAnnotation::new(
                func,
                vec![assertion],
            )
        }
        _ => unimplemented!("Need annotation for term {}", term),
    }
}
