use std::collections::HashMap;

use cranelift_isle::ast;

use cranelift_isle::ast::Defs;
use cranelift_isle::ast::Ident;
use cranelift_isle::ast::SpecExpr;
use cranelift_isle::ast::SpecOp;
use cranelift_isle::lexer::Pos;
use cranelift_isle::sema::TypeEnv;
use veri_ir::annotation_ir::{BoundVar, Const, Expr, TermAnnotation, TermSignature, Type};

static RESULT: &str = "result";

#[derive(Clone, Debug)]
pub struct AnnotationEnv {
    pub annotation_map: HashMap<String, TermAnnotation>,
}

impl AnnotationEnv {
    pub fn new(annotation_env: HashMap<String, TermAnnotation>) -> Self {
        AnnotationEnv {
            annotation_map: annotation_env,
        }
    }

    pub fn get_annotation_for_term(&self, term: &str) -> Option<TermAnnotation> {
        if self.annotation_map.contains_key(term) {
            return Some(self.annotation_map[term].clone());
        }
        None
    }
}

pub fn string_from_ident(typeenv: &TypeEnv, id: &ast::Ident) -> String {
    let sym = typeenv.sym_map[&id.0];
    typeenv.syms[sym.index()].clone()
}

pub fn spec_to_annotation_bound_var(i: &Ident, typeenv: &TypeEnv) -> BoundVar {
    // AVH TODO: handle case where bound var name differs spec to decl
    BoundVar {
        name: string_from_ident(typeenv, i),
        ty: None,
    }
}

fn spec_to_usize(s: &SpecExpr) -> usize {
    match s {
        SpecExpr::ConstInt { val, pos } => *val as usize,
        _ => unreachable!(),
    }
}

fn spec_op_to_expr(s: &SpecOp, args: &Vec<SpecExpr>, pos: &Pos, typeenv: &TypeEnv) -> Expr {
    fn unop<F: Fn(Box<Expr>, u32) -> Expr>(
        u: F,
        args: &Vec<SpecExpr>,
        pos: &Pos,
        typeenv: &TypeEnv,
    ) -> Expr {
        assert_eq!(
            args.len(),
            1,
            "Unexpected number of args for unary operator {:?}",
            pos
        );
        return u(Box::new(spec_to_expr(&args[0], typeenv)), 0);
    }
    fn binop<F: Fn(Box<Expr>, Box<Expr>, u32) -> Expr>(
        b: F,
        args: &Vec<SpecExpr>,
        pos: &Pos,
        typeenv: &TypeEnv,
    ) -> Expr {
        assert_eq!(
            args.len(),
            2,
            "Unexpected number of args for binary operator {:?}",
            pos
        );
        return b(
            Box::new(spec_to_expr(&args[0], typeenv)),
            Box::new(spec_to_expr(&args[0], typeenv)),
            0,
        );
    }

    fn variadic_binop<F: Fn(Box<Expr>, Box<Expr>, u32) -> Expr>(
        b: F,
        args: &Vec<SpecExpr>,
        pos: &Pos,
        typeenv: &TypeEnv,
    ) -> Expr {
        assert!(
            args.len() >= 1,
            "Unexpected number of args for variadic binary operator {:?}",
            pos
        );
        let mut expr_args: Vec<Expr> = args.iter().map(|a| spec_to_expr(&a, typeenv)).collect();
        let last = expr_args.remove(expr_args.len() - 1);

        // Reverse to keep the order of the original list
        expr_args
            .iter()
            .rev()
            .fold(last, |acc, a| b(Box::new(acc), Box::new(a.clone()), 0))
    }

    match s {
        // Unary
        SpecOp::Not => unop(|x, i| Expr::Not(x, i), args, pos, typeenv),
        SpecOp::BVNot => unop(|x, i| Expr::BVNot(x, i), args, pos, typeenv),
        SpecOp::BVNeg => unop(|x, i| Expr::BVNeg(x, i), args, pos, typeenv),
        SpecOp::Rev => unop(|x, i| Expr::Rev(x, i), args, pos, typeenv),

        // Variadic binops
        SpecOp::And => variadic_binop(|x, y, i| Expr::And(x, y, i), args, pos, typeenv),
        SpecOp::Or => variadic_binop(|x, y, i| Expr::Or(x, y, i), args, pos, typeenv),

        // Binary
        SpecOp::Eq => binop(|x, y, i| Expr::Eq(x, y, i), args, pos, typeenv),
        SpecOp::Lt => binop(|x, y, i| Expr::Lt(x, y, i), args, pos, typeenv),
        SpecOp::Lte => binop(|x, y, i| Expr::Lte(x, y, i), args, pos, typeenv),
        SpecOp::Gt => binop(|x, y, i| Expr::Lt(y, x, i), args, pos, typeenv),
        SpecOp::Gte => binop(|x, y, i| Expr::Lte(y, x, i), args, pos, typeenv),
        SpecOp::BVAnd => binop(|x, y, i| Expr::BVAnd(x, y, i), args, pos, typeenv),
        SpecOp::BVOr => binop(|x, y, i| Expr::BVOr(x, y, i), args, pos, typeenv),
        SpecOp::BVXor => binop(|x, y, i| Expr::BVXor(x, y, i), args, pos, typeenv),
        SpecOp::BVAdd => binop(|x, y, i| Expr::BVAdd(x, y, i), args, pos, typeenv),
        SpecOp::BVSub => binop(|x, y, i| Expr::BVSub(x, y, i), args, pos, typeenv),
        SpecOp::BVMul => binop(|x, y, i| Expr::BVMul(x, y, i), args, pos, typeenv),
        SpecOp::BVUdiv => binop(|x, y, i| Expr::BVUDiv(x, y, i), args, pos, typeenv),
        SpecOp::BVUrem => binop(|x, y, i| Expr::BVUrem(x, y, i), args, pos, typeenv),
        SpecOp::BVSdiv => binop(|x, y, i| Expr::BVXor(x, y, i), args, pos, typeenv),
        SpecOp::BVSrem => binop(|x, y, i| Expr::BVSrem(x, y, i), args, pos, typeenv),
        SpecOp::BVShl => binop(|x, y, i| Expr::BVShl(x, y, i), args, pos, typeenv),
        SpecOp::BVLshr => binop(|x, y, i| Expr::BVShr(x, y, i), args, pos, typeenv),
        SpecOp::BVAshr => binop(|x, y, i| Expr::BVAShr(x, y, i), args, pos, typeenv),
        SpecOp::BVUle => binop(|x, y, i| Expr::BVUlte(x, y, i), args, pos, typeenv),
        SpecOp::BVUlt => binop(|x, y, i| Expr::BVUlt(x, y, i), args, pos, typeenv),
        SpecOp::BVUgt => binop(|x, y, i| Expr::BVUgt(x, y, i), args, pos, typeenv),
        SpecOp::BVUge => binop(|x, y, i| Expr::BVUgte(x, y, i), args, pos, typeenv),
        SpecOp::BVSlt => binop(|x, y, i| Expr::BVSlt(x, y, i), args, pos, typeenv),
        SpecOp::BVSle => binop(|x, y, i| Expr::BVSlte(x, y, i), args, pos, typeenv),
        SpecOp::BVSgt => binop(|x, y, i| Expr::BVSgt(x, y, i), args, pos, typeenv),
        SpecOp::BVSge => binop(|x, y, i| Expr::BVSgte(x, y, i), args, pos, typeenv),
        SpecOp::Rotr => binop(|x, y, i| Expr::BVRotr(x, y, i), args, pos, typeenv),
        SpecOp::Rotl => binop(|x, y, i| Expr::BVRotl(x, y, i), args, pos, typeenv),
        // AVH TODO
        SpecOp::ZeroExt => binop(
            |x, y, i| Expr::BVZeroExtToVarWidth(x, y, i),
            args,
            pos,
            typeenv,
        ),
        SpecOp::SignExt => binop(
            |x, y, i| Expr::BVSignExtToVarWidth(x, y, i),
            args,
            pos,
            typeenv,
        ),

        // AVH TODO
        SpecOp::Concat => todo!(),
        SpecOp::Extract => {
            assert_eq!(
                args.len(),
                3,
                "Unexpected number of args for extract operator {:?}",
                pos
            );
            Expr::BVExtract(spec_to_usize(&args[0]), spec_to_usize(&args[1]), Box::new(spec_to_expr(&args[2], typeenv)), 0)
        }
        SpecOp::Subs => todo!(),
        SpecOp::Popcnt => todo!(),
        SpecOp::Clz => todo!(),
        SpecOp::Cls => todo!(),
        SpecOp::ConvTo => todo!(),
        SpecOp::Int2BV => todo!(),
        SpecOp::BV2Int => todo!(),
        SpecOp::WidthOf => todo!(),
        SpecOp::If => todo!(),
        SpecOp::Switch => todo!(),
    }
}

fn spec_to_expr(s: &SpecExpr, typeenv: &TypeEnv) -> Expr {
    match s {
        SpecExpr::ConstInt { val, pos } => Expr::Const(
            Const {
                ty: Type::Int,
                value: *val,
                width: 0,
            },
            0,
        ),
        SpecExpr::ConstBitVec { val, width, pos } => Expr::Const(
            Const {
                ty: Type::BitVectorWithWidth(*width as usize),
                value: *val,
                width: (*width as usize),
            },
            0,
        ),
        SpecExpr::ConstBool { val, pos } => Expr::Const(
            Const {
                ty: Type::Bool,
                value: *val as i128,
                width: 0,
            },
            0,
        ),
        SpecExpr::Var { var, pos } => Expr::Var(string_from_ident(typeenv, var), 0),
        SpecExpr::Op { op, args, pos } => spec_op_to_expr(op, args, pos, typeenv),
        SpecExpr::Pair { l, r } => todo!(),
        SpecExpr::Enum { name } => todo!(),
    }
}

pub fn parse_annotations(defs: &Defs, typeenv: &TypeEnv) -> AnnotationEnv {
    let mut annotation_map = HashMap::new();

    // Traverse defs to process spec annotations
    for def in &defs.defs {
        match def {
            &ast::Def::Spec(ref spec) => {
                let termname = string_from_ident(typeenv, &spec.term);
                // dbg!(&termname);
                let sig = TermSignature {
                    args: spec
                        .args
                        .iter()
                        .map(|a| spec_to_annotation_bound_var(a, typeenv))
                        .collect(),
                    ret: BoundVar {
                        name: RESULT.to_string(),
                        ty: None,
                    },
                };

                let mut assumptions = vec![];
                let mut assertions = vec![];
                for a in &spec.provides {
                    assertions.push(Box::new(spec_to_expr(a, typeenv)));
                }

                for a in &spec.requires {
                    assumptions.push(Box::new(spec_to_expr(a, typeenv)));
                }

                let annotation = TermAnnotation {
                    sig,
                    assumptions,
                    assertions,
                };
                annotation_map.insert(termname, annotation);
            }
            _ => {}
        }
    }
    AnnotationEnv { annotation_map }
}
