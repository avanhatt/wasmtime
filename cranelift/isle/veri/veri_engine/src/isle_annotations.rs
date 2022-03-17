/// This file will be replaced by a parser that consumes annotations and produces
/// the same type of structure, but for now, manually construct these annotations.
use veri_ir::annotation_ir::{
    BoundVar, Const, Expr, Function, FunctionApplication, FunctionType, TermAnnotation,
    TermSignature, Type,
};

pub fn isle_annotation_for_term(term: &str) -> Option<TermAnnotation> {
    match term {
        // (spec (sig (args (x: bvX) (ret: bvX))
        //       (assumptions (= x ret)))
        "lower" | "put_in_reg" | "value_reg" | "first_result" | "inst_data" => {
            // No-op for now
            let arg = BoundVar::new("arg");
            let result = BoundVar::new("ret");
            let identity = Expr::binary(Expr::Eq, arg.as_expr(), result.as_expr());
            let func = TermSignature {
                args: vec![arg],
                ret: result,
            };
            Some(TermAnnotation::new(func, vec![identity]))
        }
        "InstructionData.Binary" => {
            // List must have length 2 since it's a Binary
            let list_ty = Type::BitVectorList(2);
            let arg_list = BoundVar::new("arg_list");
            let result = BoundVar::new("ret");

            let opcode = BoundVar::new_with_ty(
                "opcode",
                &Type::Function(FunctionType {
                    args: vec![list_ty],
                    ret: Box::new(Type::BitVector),
                }),
            );

            let app = Expr::FunctionApplication(FunctionApplication {
                func: Box::new(opcode.as_expr()),
                args: vec![arg_list.as_expr()],
            });
            let eq = Expr::binary(Expr::Eq, app, result.as_expr());

            let func = TermSignature {
                args: vec![opcode, arg_list],
                ret: result,
            };
            Some(TermAnnotation::new(func, vec![eq]))
        }
        "value_type" => {
            let arg = BoundVar::new("arg");
            let result = BoundVar::new("ret");
            let ty_eq = Expr::binary(Expr::Eq, arg.as_expr(), Expr::TyWidth);
            let func = TermSignature {
                args: vec![arg],
                ret: result,
            };
            Some(TermAnnotation::new(func, vec![ty_eq]))
        }
        "value_array_2" => {
            let arg1 = BoundVar::new("arg1");
            let arg2 = BoundVar::new("arg2");
            let result = BoundVar::new("ret");

            let ls = Expr::List(vec![arg1.as_expr(), arg2.as_expr()]);
            let eq = Expr::binary(Expr::Eq, ls, result.as_expr());

            let func = TermSignature {
                args: vec![arg1, arg2],
                ret: result,
            };
            Some(TermAnnotation::new(func, vec![eq]))
        }
        // (spec (sig (args x: bvX) (ret: bvX))
        //       (assumptions (= x ret)))
        "has_type" => {
            // Add an assertion on the type
            let ty_arg = BoundVar::new("ty");
            let arg = BoundVar::new("arg");
            let result = BoundVar::new("ret");
            let ty_eq = Expr::binary(Expr::Eq, ty_arg.as_expr(), Expr::TyWidth);
            let identity = Expr::binary(Expr::Eq, arg.as_expr(), result.as_expr());
            let func = TermSignature {
                args: vec![ty_arg, arg],
                ret: result,
            };
            Some(TermAnnotation::new(func, vec![ty_eq, identity]))
        }
        "fits_in_64" => {
            // Identity, but add assertion on type
            let arg = BoundVar::new("arg");
            let result = BoundVar::new("ret");
            let identity = Expr::binary(Expr::Eq, arg.as_expr(), result.as_expr());
            let ty_fits = Expr::binary(
                Expr::Lte,
                arg.as_expr(),
                Expr::Const(Const {
                    ty: Type::Int,
                    value: 64_i128,
                }),
            );
            let func = TermSignature {
                args: vec![arg],
                ret: result,
            };
            Some(TermAnnotation::new(func, vec![identity, ty_fits]))
        }
        // "iadd" => {
        //     let a = BoundVar::new("a");
        //     let b = BoundVar::new("b");
        //     let r = BoundVar::new("r");
        //     let sem = Expr::binary(
        //         Expr::Eq,
        //         Expr::binary(Expr::BVAdd, a.as_expr(), b.as_expr()),
        //         r.as_expr(),
        //     );
        //     let func = TermSignature {
        //         args: vec![a, b],
        //         ret: r,
        //     };
        //     Some(TermAnnotation::new(func, vec![sem]))
        // }
        "Opcode.Iadd" => {
            let value_list = BoundVar::new("xs");
            let r = BoundVar::new("r");
            let x = Expr::GetElement(Box::new(value_list.as_expr()), 0);
            let y = Expr::GetElement(Box::new(value_list.as_expr()), 1);
            let body = Expr::binary(Expr::BVAdd, x, y);
            let func_expr = Expr::Function(Function {
                name: "Opcode.Iadd".to_string(),
                args: vec![value_list],
                ty: Type::Function(FunctionType {
                    args: vec![Type::BitVectorList(2)],
                    ret: Box::new(Type::BitVector),
                }),
                body: Box::new(body),
            });
            let body_semantics = Expr::binary(Expr::Eq, r.as_expr(), func_expr);
            // The opcode itself takes no arguments
            let func = TermSignature {
                args: vec![],
                ret: r,
            };
            Some(TermAnnotation::new(func, vec![body_semantics]))
        }
        "add" => {
            let t = BoundVar::new("ty");
            let a = BoundVar::new("a");
            let b = BoundVar::new("b");
            let r = BoundVar::new("r");
            let sem = Expr::binary(
                Expr::Eq,
                Expr::binary(Expr::BVAdd, a.as_expr(), b.as_expr()),
                r.as_expr(),
            );
            let func = TermSignature {
                args: vec![t, a, b],
                ret: r,
            };
            Some(TermAnnotation::new(func, vec![sem]))
        }
        "imm12_from_negated_value" => {
            // Width: bv12
            let imm_arg = BoundVar::new("imm_arg");

            // Width: bvX
            let result = BoundVar::new("ret");

            // Negate and convert
            let as_ty = Expr::BVConvFrom(12, Box::new(imm_arg.as_expr()));
            let res = Expr::unary(Expr::BVNeg, as_ty);
            let eq = Expr::binary(Expr::Eq, res, result.as_expr());
            let sig = TermSignature {
                args: vec![imm_arg],
                ret: result,
            };
            Some(TermAnnotation::new(sig, vec![eq]))
        }
        "sub_imm" => {
            // Declare bound variables
            let ty_arg = BoundVar::new("ty");
            let reg_arg = BoundVar::new("reg");
            let result = BoundVar::new("ret");

            // Width: bv12
            let imm_arg = BoundVar::new("imm_arg");

            // Conversion step
            let as_ty = Expr::BVConvFrom(12, Box::new(imm_arg.as_expr()));
            let res = Expr::binary(Expr::BVSub, reg_arg.as_expr(), as_ty);
            let assertion = Expr::binary(Expr::Eq, res, result.as_expr());
            let func = TermSignature {
                args: vec![ty_arg, reg_arg, imm_arg],
                ret: result,
            };
            Some(TermAnnotation::new(func, vec![assertion]))
        }
        _ => None,
    }
}
