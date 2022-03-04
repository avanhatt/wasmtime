/// This file will be replaced by a parser that consumes annotations and produces
/// the same type of structure, but for now, manually construct these annotations.
use std::cmp::Ordering;
use veri_ir::{BoundVar, Function, FunctionAnnotation, VIRAnnotation, VIRExpr, VIRType};

pub fn isle_annotation_for_term(term: &str, ty: &VIRType) -> Option<VIRAnnotation> {
    match term {
        "lower" | "put_in_reg" | "value_reg" | "first_result" | "inst_data" => {
            // No-op for now
            let arg = BoundVar::new("arg", ty);
            let result = BoundVar::new("ret", ty);
            let identity = VIRType::eq(arg.as_expr(), result.as_expr());
            let func = FunctionAnnotation {
                args: vec![arg],
                ret: result,
            };
            Some(VIRAnnotation::new(func, vec![identity]))
        }
        "InstructionData.Binary" => {
            // List must have length 2 since it's a Binary
            let list_ty = ty.list_ty(2);
            let arg_list = BoundVar::new("arg_list", &list_ty);
            let result = BoundVar::new("ret", ty);

            let opcode = BoundVar::new(
                "opcode",
                &VIRType::Function(vec![list_ty], Box::new(ty.clone())),
            );

            let app = ty.clone().apply(opcode.as_expr(), vec![arg_list.as_expr()]);
            let eq = VIRType::eq(app, result.as_expr());

            let func = FunctionAnnotation {
                args: vec![opcode, arg_list],
                ret: result,
            };
            Some(VIRAnnotation::new(func, vec![eq]))
        }
        "value_type" => {
            let arg = BoundVar::new("arg", &VIRType::IsleType);
            let result = BoundVar::new("ret", ty);
            let ty_eq = VIRType::eq(
                arg.as_expr(),
                VIRType::IsleType.isle_type_const(ty.width() as i128),
            );
            let func = FunctionAnnotation {
                args: vec![arg],
                ret: result,
            };
            Some(VIRAnnotation::new(func, vec![ty_eq]))
        }
        "value_array_2" => {
            let arg1 = BoundVar::new("arg1", &ty.element_ty());
            let arg2 = BoundVar::new("arg2", &ty.element_ty());

            let ls = ty.list(vec![arg1.as_expr(), arg2.as_expr()]);

            let result = BoundVar::new("ret", &ls.ty().clone());
            let eq = VIRType::eq(ls, result.as_expr());

            let func = FunctionAnnotation {
                args: vec![arg1, arg2],
                ret: result,
            };
            Some(VIRAnnotation::new(func, vec![eq]))
        }
        "has_type" => {
            // Add an assertion on the type
            let ty_arg = BoundVar::new("y", &VIRType::IsleType);
            let arg = BoundVar::new("arg", ty);
            let result = BoundVar::new("ret", ty);
            let ty_eq = VIRType::eq(
                ty_arg.as_expr(),
                VIRType::IsleType.isle_type_const(ty.width() as i128),
            );
            let identity = VIRType::eq(arg.as_expr(), result.as_expr());
            let func = FunctionAnnotation {
                args: vec![ty_arg, arg],
                ret: result,
            };
            Some(VIRAnnotation::new(func, vec![ty_eq, identity]))
        }
        "fits_in_64" => {
            // Identity, but add assertion on type
            let arg = BoundVar::new("arg", ty);
            let result = BoundVar::new("ret", ty);
            let identity = VIRType::eq(arg.as_expr(), result.as_expr());
            let ty_fits = VIRType::lte(arg.as_expr(), VIRType::IsleType.isle_type_const(64_i128));
            let func = FunctionAnnotation {
                args: vec![arg],
                ret: result,
            };
            Some(VIRAnnotation::new(func, vec![identity, ty_fits]))
        }
        "iadd" => {
            let a = BoundVar::new("a", ty);
            let b = BoundVar::new("b", ty);
            let r = BoundVar::new("r", ty);
            let sem = VIRType::eq(
                ty.bv_binary(VIRExpr::BVAdd, a.as_expr(), b.as_expr()),
                r.as_expr(),
            );
            let func = FunctionAnnotation {
                args: vec![a, b],
                ret: r,
            };
            Some(VIRAnnotation::new(func, vec![sem]))
        }
        "Opcode.Iadd" => {
            let value_list = BoundVar::new("xs", &ty.function_arg_types()[0]);
            let list_ty = value_list.ty.clone();
            let r = BoundVar::new("r", ty);
            let sig = Function {
                name: "Opcode.Iadd".to_string(),
                args: vec![value_list.clone()],
                ty: ty.clone(),
            };
            let x = list_ty.get_element(value_list.as_expr(), 0);
            let y = list_ty.get_element(value_list.as_expr(), 1);
            let body = x.clone().ty().bv_binary(VIRExpr::BVAdd, x, y);
            let func_expr = VIRExpr::Function(sig, Box::new(body));
            let body_semantics = VIRType::eq(r.as_expr(), func_expr);
            // The opcode itself takes no arguments
            let func = FunctionAnnotation {
                args: vec![],
                ret: r,
            };
            Some(VIRAnnotation::new(func, vec![body_semantics]))
        }
        "add" => {
            let t = BoundVar::new("ty", &VIRType::IsleType);
            let a = BoundVar::new("a", ty);
            let b = BoundVar::new("b", ty);
            let r = BoundVar::new("r", ty);
            let sem = VIRType::eq(
                ty.bv_binary(VIRExpr::BVAdd, a.as_expr(), b.as_expr()),
                r.as_expr(),
            );
            let func = FunctionAnnotation {
                args: vec![t, a, b],
                ret: r,
            };
            Some(VIRAnnotation::new(func, vec![sem]))
        }
        "imm12_from_negated_value" => {
            let bv12 = VIRType::BitVector(12);
            let imm_arg = BoundVar::new("imm_arg", &bv12);
            let result = BoundVar::new("ret", ty);

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
            Some(VIRAnnotation::new(func, vec![assume_fits, res_assertion]))
        }
        "sub_imm" => {
            let bv12 = VIRType::BitVector(12);

            // Declare bound variables
            let ty_arg = BoundVar::new("ty", &VIRType::IsleType);
            let reg_arg = BoundVar::new("reg", ty);
            let imm_arg = BoundVar::new("imm_arg", &bv12);
            let result = BoundVar::new("ret", ty);

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
            Some(VIRAnnotation::new(func, vec![assertion]))
        }
        _ => None,
    }
}
