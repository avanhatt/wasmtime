use std::cmp::Ordering;
use std::collections::HashMap;

use veri_ir::{annotation_ir, Function, FunctionApplication};
use veri_ir::{BoundVar, VIRExpr, VIRTermAnnotation, VIRTermSignature, VIRType};

use cranelift_isle as isle;
use isle::sema::{TypeEnv, TypeId};
use veri_annotation::parser_wrapper::AnnotationEnv;

const REG_WIDTH: usize = 64;

#[derive(Clone, Debug)]
pub struct TypeContext<'ctx> {
    // Default bitvector type
    pub ty: VIRType,

    // Pointers to ISLE environments
    typeenv: &'ctx TypeEnv,

    // Isle annotations
    annotation_env: &'ctx AnnotationEnv,

    // Map of bound variables to types
    var_types: HashMap<String, VIRType>,
}

impl<'ctx> TypeContext<'ctx> {
    pub fn new(typeenv: &'ctx TypeEnv, annotation_env: &'ctx AnnotationEnv, ty: VIRType) -> Self {
        assert!(ty.is_bv());
        TypeContext {
            typeenv,
            annotation_env,
            ty,
            var_types: HashMap::new(),
        }
    }

    /// An approximation for now: types from CLIF type names
    pub fn vir_type_for_type_id(&self, typeid: TypeId) -> VIRType {
        let clif_name = match &self.typeenv.types[typeid.index()] {
            &isle::sema::Type::Primitive(_, sym, _) | &isle::sema::Type::Enum { name: sym, .. } => {
                self.typeenv.syms[sym.index()].clone()
            }
        };
        println!("vir_type_for_type_id: {}", clif_name);

        match clif_name.as_str() {
            // primitive types
            "bool" => VIRType::Bool,
            "u8" => VIRType::BitVector(8),

            // custom types
            "Type" => VIRType::Int,
            "Imm12" => VIRType::BitVector(12),
            "Imm64" => VIRType::BitVector(64),
            "ImmShift" => VIRType::BitVector(6),
            "ImmLogic" => VIRType::BitVector(12),
            "u64" => VIRType::BitVector(64),
            "MoveWideConst" => VIRType::BitVector(16),
            "OperandSize" => self.ty.clone(),
            // TODO: should probably update this logic to use an actual
            // register width for some of these
            "Reg" | "ValueRegs" => VIRType::BitVector(REG_WIDTH),
            "Inst" | "Value" | /*"ValueRegs" |*/ "InstructionData" => self.ty.clone(),

            // For now, hard code errors for these types that we later want to
            // explicitly mark as unsafe.
            "Opcode" => unreachable!(),
            "ALUOp" => unreachable!(),
            "ValueArray2" => unreachable!(),
            "MInst" => unreachable!(),
            _ => unimplemented!("ty: {}", clif_name),
        }
    }

    fn compatible_types(high_level: &Option<annotation_ir::Type>, vir: &VIRType) -> bool {
        match (high_level, vir) {
            (None, _) => true,
            (Some(annotation_ir::Type::Bool), VIRType::Bool) => true,
            (Some(annotation_ir::Type::Int), VIRType::Int) => true,
            (Some(annotation_ir::Type::BitVector), VIRType::BitVector(..)) => true,
            (Some(annotation_ir::Type::BitVectorList(l1)), VIRType::BitVectorList(l2, _)) => {
                *l1 == *l2
            }
            (Some(annotation_ir::Type::Function(func)), VIRType::Function(args, ret)) => {
                func.args
                    .iter()
                    .zip(args)
                    .all(|(a1, a2)| Self::compatible_types(&Some(a1.clone()), a2))
                    && Self::compatible_types(&Some(*func.ret.clone()), &*ret)
            }
            _ => false,
        }
    }

    fn type_bound_var(&mut self, v: &annotation_ir::BoundVar, ty: VIRType) -> BoundVar {
        assert!(
            Self::compatible_types(&v.ty, &ty),
            "Incompatible high level and VIR types ({:?}. {:?})",
            v.ty,
            ty
        );
        self.var_types.insert(v.name.clone(), ty.clone());
        BoundVar {
            name: v.name.clone(),
            ty,
        }
    }

    fn concretize_type(&self, ty: &annotation_ir::Type) -> VIRType {
        match ty {
            annotation_ir::Type::BitVector => VIRType::BitVector(self.ty.width()),
            annotation_ir::Type::BitVectorList(len) => {
                VIRType::BitVectorList(*len, self.ty.width())
            }
            annotation_ir::Type::Int => VIRType::Int,
            annotation_ir::Type::Function(func) => VIRType::Function(
                func.args.iter().map(|a| self.concretize_type(a)).collect(),
                Box::new(self.concretize_type(&*func.ret)),
            ),
            annotation_ir::Type::Bool => VIRType::Bool,
        }
    }

    fn type_expr(&mut self, term: &annotation_ir::Expr) -> VIRExpr {
        let expect_boxed = |e: &annotation_ir::Expr, ctx: &mut Self| {
            let ve = ctx.type_expr(&*e);
            Box::new(ve)
        };
        let expect_boxed_bool = |e: &annotation_ir::Expr, ctx: &mut Self| {
            let ve = ctx.type_expr(&*e);
            assert!(ve.ty().is_bool(), "expect_boxed_bool got {:?}", ve);
            Box::new(ve)
        };
        let expect_boxed_bv = |e: &annotation_ir::Expr, ctx: &mut Self| {
            let ve = ctx.type_expr(&*e);
            assert!(ve.ty().is_bv(), "expect_boxed_bv got {:?}", ve);
            Box::new(ve)
        };
        let expect_boxed_int = |e: &annotation_ir::Expr, ctx: &mut Self| {
            let ve = ctx.type_expr(&*e);
            assert!(ve.ty().is_int(), "expect_boxed_int got {:?}", ve);
            Box::new(ve)
        };
        match term {
            annotation_ir::Expr::Var(s) => VIRExpr::Var(BoundVar {
                name: s.clone(),
                ty: self.var_types.get(s).unwrap().clone(),
            }),
            annotation_ir::Expr::Const(c) => match c.ty {
                annotation_ir::Type::Int => VIRExpr::Const(VIRType::Int, c.value),
                annotation_ir::Type::BitVector => {
                    VIRExpr::Const(VIRType::BitVector(c.width), c.value)
                }
                _ => todo!("Non-integer constants"),
            },
            annotation_ir::Expr::True => VIRExpr::True,
            annotation_ir::Expr::False => VIRExpr::False,
            annotation_ir::Expr::TyWidth => VIRExpr::Const(VIRType::Int, self.ty.width() as i128),
            annotation_ir::Expr::WidthOf(x) => {
                VIRExpr::WidthOf(Box::new(self.type_expr(&*x)))
            }
            annotation_ir::Expr::Not(e) => VIRExpr::Not(expect_boxed_bool(e, self)),
            annotation_ir::Expr::And(x, y) => {
                VIRExpr::And(expect_boxed_bool(x, self), expect_boxed_bool(y, self))
            }
            annotation_ir::Expr::Or(x, y) => {
                VIRExpr::Or(expect_boxed_bool(x, self), expect_boxed_bool(y, self))
            }
            annotation_ir::Expr::Imp(x, y) => {
                VIRExpr::Imp(expect_boxed_bool(x, self), expect_boxed_bool(y, self))
            }
            annotation_ir::Expr::Eq(x, y) => {
                let vx = expect_boxed(x, self);
                let vy = expect_boxed(y, self);
                assert_eq!(vx.ty(), vy.ty(), "= {:?} {:?}", vx, vy);
                VIRExpr::Eq(vx, vy)
            }
            annotation_ir::Expr::Lte(x, y) => {
                let vx = expect_boxed(x, self);
                let vy = expect_boxed(y, self);
                assert_eq!(vx.ty(), vy.ty());
                VIRExpr::Lte(vx, vy)
            }
            annotation_ir::Expr::BVNeg(x) => {
                let vx = expect_boxed_bv(x, self);
                assert!(vx.ty().is_bv());
                VIRExpr::BVNeg(vx.ty().clone(), vx)
            }
            annotation_ir::Expr::BVNot(x) => {
                let vx = expect_boxed_bv(x, self);
                assert!(vx.ty().is_bv());
                VIRExpr::BVNot(vx.ty().clone(), vx)
            }
            annotation_ir::Expr::BVAdd(x, y) => {
                let vx = expect_boxed_bv(x, self);
                let vy = expect_boxed_bv(y, self);
                assert_eq!(vx.ty(), vy.ty());
                assert!(vx.ty().is_bv());
                VIRExpr::BVAdd(vx.ty().clone(), vx, vy)
            }
            annotation_ir::Expr::BVSub(x, y) => {
                let vx = expect_boxed_bv(x, self);
                let vy = expect_boxed_bv(y, self);
                assert_eq!(vx.ty(), vy.ty());
                assert!(vx.ty().is_bv());
                VIRExpr::BVSub(vx.ty().clone(), vx, vy)
            }
            annotation_ir::Expr::BVAnd(x, y) => {
                let vx = expect_boxed_bv(x, self);
                let vy = expect_boxed_bv(y, self);
                assert_eq!(vx.ty(), vy.ty());
                assert!(vx.ty().is_bv());
                VIRExpr::BVAnd(vx.ty().clone(), vx, vy)
            }
            annotation_ir::Expr::BVOr(x, y) => {
                let vx = expect_boxed_bv(x, self);
                let vy = expect_boxed_bv(y, self);
                assert_eq!(vx.ty(), vy.ty());
                assert!(vx.ty().is_bv());
                VIRExpr::BVOr(vx.ty().clone(), vx, vy)
            }
            annotation_ir::Expr::BVRotl(x, y) => {
                let vx = expect_boxed_bv(x, self);
                let vy = expect_boxed_bv(y, self);
                assert_eq!(vx.ty(), vy.ty());
                assert!(vx.ty().is_bv());
                VIRExpr::BVRotl(vx.ty().clone(), vx, vy)
            }
            annotation_ir::Expr::BVShl(x, y) => {
                let vx = expect_boxed_bv(x, self);
                let vy = expect_boxed_bv(y, self);
                assert_eq!(vx.ty(), vy.ty());
                assert!(vx.ty().is_bv());
                VIRExpr::BVShl(vx.ty().clone(), vx, vy)
            }
            annotation_ir::Expr::BVShr(x, y) => {
                let vx = expect_boxed_bv(x, self);
                let vy = expect_boxed_bv(y, self);
                assert_eq!(vx.ty(), vy.ty());
                assert!(vx.ty().is_bv());
                VIRExpr::BVShr(vx.ty().clone(), vx, vy)
            }
            annotation_ir::Expr::BVZeroExt(i, x) => {
                let vx = expect_boxed_bv(x, self);
                assert!(vx.ty().is_bv());
                let new_width = vx.ty().width() + *i;
                VIRExpr::BVZeroExt(VIRType::BitVector(new_width), *i, vx)
            }
            annotation_ir::Expr::BVSignExt(i, x) => {
                let vx = expect_boxed_bv(x, self);
                assert!(vx.ty().is_bv());
                let new_width = vx.ty().width() + *i;
                VIRExpr::BVSignExt(VIRType::BitVector(new_width), *i, vx)
            }
            annotation_ir::Expr::BVExtract(l, h, x) => {
                let vx = expect_boxed_bv(x, self);
                assert!(vx.ty().is_bv());
                assert!(*h >= *l);
                let new_width = *h - *l + 1;
                VIRExpr::BVExtract(VIRType::BitVector(new_width), *l, *h, vx)
            }
            annotation_ir::Expr::BVConvTo(dest, x) => {
                let vx = expect_boxed_bv(x, self);
                assert!(vx.ty().is_bv() || vx.ty().is_int());
                assert!(self.ty.is_bv());
                let width = match **dest {
                    annotation_ir::Width::Const(c) => c,
                    annotation_ir::Width::RegWidth => REG_WIDTH,
                };
                let new_ty = VIRType::BitVector(width);
                match vx.ty() {
                    VIRType::BitVector(w) => {
                        let width_diff = (width as i128) - (*w as i128);
                        match width_diff.cmp(&0) {
                            Ordering::Less => VIRExpr::BVExtract(new_ty, 0, width - 1, vx),
                            Ordering::Greater => {
                                VIRExpr::BVZeroExt(new_ty, width_diff.try_into().unwrap(), vx)
                            }
                            Ordering::Equal => *vx,
                        }
                    }
                    _ => unreachable!("{:?}", vx.ty())
                }
            }
            annotation_ir::Expr::BVConvFrom(src, x) => {
                let vx = expect_boxed_bv(x, self);
                assert!(vx.ty().is_bv());
                assert!(self.ty.is_bv());
                assert_eq!(vx.ty().width(), *src);
                let width_diff = (self.ty.width() as i128) - (vx.ty().width() as i128);
                let new_ty = VIRType::BitVector(self.ty.width());
                match width_diff.cmp(&0) {
                    Ordering::Less => VIRExpr::BVExtract(new_ty, 0, self.ty.width() - 1, vx),
                    Ordering::Greater => {
                        VIRExpr::BVZeroExt(new_ty, width_diff.try_into().unwrap(), vx)
                    }
                    Ordering::Equal => *vx,
                }
            }
            annotation_ir::Expr::BVIntToBv(width, x) => {
                let width = expect_boxed_bv(width, self);
                let vx = expect_boxed_int(x, self);
                VIRExpr::BVIntToBV(width.ty().clone(), vx)
            }
            annotation_ir::Expr::Function(f) => {
                let func_ty = self.concretize_type(&f.ty);
                let args = f
                    .args
                    .iter()
                    .enumerate()
                    .map(|(i, a)| self.type_bound_var(a, func_ty.function_arg_types()[i].clone()))
                    .collect();
                let body = Box::new(self.type_expr(&f.body));
                VIRExpr::Function(Function {
                    name: f.name.clone(),
                    ty: func_ty,
                    args,
                    body,
                })
            }
            annotation_ir::Expr::FunctionApplication(app) => {
                let func = expect_boxed(&app.func, self);
                let args: Vec<VIRExpr> = app.args.iter().map(|a| self.type_expr(a)).collect();
                for (i, a) in args.iter().enumerate() {
                    assert_eq!(*a.ty(), func.ty().function_arg_types()[i]);
                }
                VIRExpr::FunctionApplication(FunctionApplication {
                    ty: func.ty().function_ret_type().clone(),
                    func,
                    args,
                })
            }
            annotation_ir::Expr::List(xs) => {
                let vs: Vec<VIRExpr> = xs.iter().map(|a| self.type_expr(a)).collect();
                // Enforce homogenous list types
                if let Some(first) = vs.first() {
                    for rest in &vs[1..] {
                        assert_eq!(first.ty(), rest.ty());
                    }
                }
                VIRExpr::List(
                    VIRType::BitVectorList(vs.len(), vs.first().unwrap().ty().width()),
                    vs,
                )
            }
            annotation_ir::Expr::GetElement(x, i) => {
                let v = self.type_expr(&*x);
                assert!(matches!(v.ty(), VIRType::BitVectorList(..)));
                VIRExpr::GetElement(v.ty().element_ty(), Box::new(v), *i)
            }
        }
    }

    pub fn typed_isle_annotation_for_term(
        &mut self,
        term: &str,
        subterm_typeids: Vec<TypeId>,
        ty: &VIRType,
    ) -> Option<VIRTermAnnotation> {
        let initial_term = self.annotation_env.get_annotation_for_term(term);
        let subterm_types: Vec<VIRType> = subterm_typeids
            .iter()
            .map(|tid| self.vir_type_for_type_id(*tid))
            .collect();
        initial_term.map(|a| {
            VIRTermAnnotation::new(
                VIRTermSignature {
                    args: a
                        .sig()
                        .args
                        .iter()
                        .enumerate()
                        .map(|(i, b)| self.type_bound_var(b, subterm_types[i].clone()))
                        .collect(),
                    ret: self.type_bound_var(&a.sig().ret, ty.clone()),
                },
                a.assertions().iter().map(|e| self.type_expr(e)).collect(),
            )
        })
    }
}
