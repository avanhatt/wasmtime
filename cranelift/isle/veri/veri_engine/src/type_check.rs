use std::cmp::Ordering;
use std::collections::HashMap;

use veri_ir::{annotation_ir, Function, FunctionApplication};
use veri_ir::{BoundVar, VIRExpr, VIRTermAnnotation, VIRTermSignature, VIRType};

use crate::isle_annotations::isle_annotation_for_term;
use cranelift_isle as isle;
use isle::sema::{TermEnv, TypeEnv, TypeId};

#[derive(Clone, Debug)]
pub struct TypeContext<'ctx> {
    // Pointers to ISLE environments
    termenv: &'ctx TermEnv,
    typeenv: &'ctx TypeEnv,

    // Default bitvector type
    ty: VIRType,

    // Map of bound variables to types
    var_types: HashMap<String, VIRType>,
}

impl<'ctx> TypeContext<'ctx> {
    pub fn new(termenv: &'ctx TermEnv, typeenv: &'ctx TypeEnv, ty: VIRType) -> Self {
        assert!(ty.is_bv());
        TypeContext {
            termenv,
            typeenv,
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
        match clif_name.as_str() {
            "Type" => VIRType::Int,
            "Imm12" => VIRType::BitVector(12),
            // TODO: should probably update this logic to use an actual
            // register width for some of these
            "Opcode" => VIRType::Function(
                vec![VIRType::BitVectorList(2, self.ty.width())],
                Box::new(self.ty.clone()),
            ),
            "ValueArray2" => VIRType::BitVectorList(2, self.ty.width()),
            "Reg" | "Inst" | "Value" | "InstructionData" => self.ty.clone(),
            _ => unimplemented!("ty: {}", clif_name),
        }
    }

    fn type_bound_var(&mut self, v: &annotation_ir::BoundVar, ty: VIRType) -> BoundVar {
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
            assert!(ve.ty().is_bool());
            Box::new(ve)
        };
        let expect_boxed_bv = |e: &annotation_ir::Expr, ctx: &mut Self| {
            let ve = ctx.type_expr(&*e);
            assert!(ve.ty().is_bv());
            Box::new(ve)
        };
        match term {
            annotation_ir::Expr::Var(s) => VIRExpr::Var(BoundVar {
                name: s.clone(),
                ty: self.var_types.get(s).unwrap().clone(),
            }),
            annotation_ir::Expr::Const(c) => match c.ty {
                annotation_ir::Type::Int => VIRExpr::Const(VIRType::Int, c.value),
                _ => todo!(),
            },
            annotation_ir::Expr::True => VIRExpr::True,
            annotation_ir::Expr::False => VIRExpr::False,
            annotation_ir::Expr::TyWidth => VIRExpr::Const(VIRType::Int, self.ty.width() as i128),
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
                assert_eq!(vx.ty(), vy.ty());
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
                assert!(vx.ty().is_bv());
                assert!(self.ty.is_bv());
                let width_diff = (*dest as i128) - (vx.ty().width() as i128);
                let new_ty = VIRType::BitVector(*dest);
                match width_diff.cmp(&0) {
                    Ordering::Less => VIRExpr::BVExtract(new_ty, 0, *dest - 1, vx),
                    Ordering::Greater => {
                        VIRExpr::BVZeroExt(new_ty, width_diff.try_into().unwrap(), vx)
                    }
                    Ordering::Equal => *vx,
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
                    ty: func.ty().function_ret_type(),
                    func,
                    args,
                })
            }
            annotation_ir::Expr::List(xs) => {
                let vs: Vec<VIRExpr> = xs.iter().map(|a| self.type_expr(a)).collect();
                VIRExpr::List(
                    VIRType::BitVectorList(vs.len(), vs.first().unwrap().ty().width()),
                    vs,
                )
            }
            annotation_ir::Expr::GetElement(x, i) => {
                let ty = if let annotation_ir::Expr::Var(s) = *x.clone() {
                    if let Some(ty) = self.var_types.get(&s) {
                        assert!(matches!(ty, VIRType::BitVectorList(..)));
                        ty.clone()
                    } else {
                        todo!("more complicated lists")
                    }
                } else {
                    todo!("more complicated lists")
                };
                let v = self.type_expr(&*x);
                VIRExpr::GetElement(ty.element_ty(), Box::new(v), *i)
            }
        }
    }

    pub fn typed_isle_annotation_for_term(
        &mut self,
        term: &str,
        subterm_typeids: Vec<TypeId>,
        ty: &VIRType,
    ) -> Option<VIRTermAnnotation> {
        let initial_term = isle_annotation_for_term(term);
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
