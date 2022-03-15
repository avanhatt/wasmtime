use std::cmp::Ordering;
use std::collections::HashMap;

use veri_ir::{annotation_ir, Function};
use veri_ir::{BoundVar, VIRExpr, VIRTermAnnotation, VIRTermSignature, VIRType};

use crate::isle_annotations::isle_annotation_for_term;
use cranelift_isle as isle;
use isle::sema::{TermEnv, TypeEnv, TypeId};

#[derive(Clone, Debug)]
pub struct TypeContext<'ctx> {
    // Pointers to ISLE environments
    termenv: &'ctx TermEnv,
    typeenv: &'ctx TypeEnv,

    // Map of bound variables to types
    var_types: HashMap<String, VIRType>,
}

impl<'ctx> TypeContext<'ctx> {
    pub fn new(termenv: &'ctx TermEnv, typeenv: &'ctx TypeEnv) -> Self {
        TypeContext {
            termenv,
            typeenv,
            var_types: HashMap::new(),
        }
    }

    /// An approximation for now: types from CLIF type names
    pub fn vir_type_for_type_id(&self, typeid: TypeId, base_ty: &VIRType) -> VIRType {
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
            "Reg" | "Inst" | "Value" => base_ty.clone(),
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

    fn type_expr(&mut self, term: &annotation_ir::Expr, ty: &VIRType) -> VIRExpr {
        let expect_boxed = |e: &Box<annotation_ir::Expr>, ctx: &mut Self| {
            let ve = ctx.type_expr(&*e, ty);
            Box::new(ve)
        };
        let expect_boxed_bool = |e: &Box<annotation_ir::Expr>,  ctx: &mut Self| {
            let ve = ctx.type_expr(&*e, ty);
            assert!(ve.ty().is_bool());
            Box::new(ve)
        };
        let expect_boxed_bv = |e: &Box<annotation_ir::Expr>,  ctx: &mut Self| {
            let ve = ctx.type_expr(&*e, ty);
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
            annotation_ir::Expr::TyWidth => VIRExpr::Const(VIRType::Int, ty.width() as i128),
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
            },
            annotation_ir::Expr::BVConvTo(dest, x) => {
                let vx = expect_boxed_bv(x, self);
                assert!(vx.ty().is_bv());
                assert!(ty.is_bv());
                let width_diff = (*dest as i128) - (vx.ty().width() as i128);
                let new_ty = VIRType::BitVector(*dest);
                match width_diff.cmp(&0) {
                    Ordering::Less => VIRExpr::BVExtract(new_ty, 0, *dest - 1, vx),
                    Ordering::Greater => VIRExpr::BVZeroExt(new_ty, width_diff.try_into().unwrap(), vx),
                    Ordering::Equal => *vx,
                }
            },
            annotation_ir::Expr::BVConvFrom(src, x) => {
                let vx = expect_boxed_bv(x, self);
                assert!(vx.ty().is_bv());
                assert!(ty.is_bv());
                assert_eq!(vx.ty().width(), *src);
                let width_diff = (ty.width() as i128) - (vx.ty().width() as i128);
                let new_ty = VIRType::BitVector(ty.width());
                match width_diff.cmp(&0) {
                    Ordering::Less => VIRExpr::BVExtract(new_ty, 0, ty.width() - 1, vx),
                    Ordering::Greater => VIRExpr::BVZeroExt(new_ty, width_diff.try_into().unwrap(), vx),
                    Ordering::Equal => *vx,
                }
            },
            annotation_ir::Expr::Function(f) => {
                // let body = expect_boxed(&f.body, self);
                // let args : Vec<BoundVar> = f.args.iter().map(|a| self.type_bound_var(a, ty.clone())).collect();
                // VIRExpr::Function(Function{
                //     name: f.name.clone(),
                //     ty: VIRType::Function(args.iter().map(|a| a.ty).collect::<Vec<VIRType>>(), Box::new(body.ty().clone())),
                //     args: f.args.iter().map(|a| self.type_bound_var(a, ty.clone())).collect(),
                //     body,
                // })
                todo!()
            }
            annotation_ir::Expr::FunctionApplication(_) => todo!(),
            annotation_ir::Expr::List(_) => todo!(),
            annotation_ir::Expr::GetElement(_, _) => todo!(),
        }
    }

    pub fn typed_isle_annotation_for_term(
        &mut self,
        term: &str,
        typeid: &TypeId,
        subterm_typeids: Vec<TypeId>,
        ty: &VIRType,
    ) -> Option<VIRTermAnnotation> {
        let initial_term = isle_annotation_for_term(term);
        let subterm_types: Vec<VIRType> = subterm_typeids
            .iter()
            .map(|tid| self.vir_type_for_type_id(tid.clone(), ty))
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
                a.assertions()
                    .iter()
                    .map(|e| self.type_expr(e, ty))
                    .collect(),
            )
        })
    }
}
