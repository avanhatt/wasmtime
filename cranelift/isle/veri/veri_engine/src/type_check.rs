use std::cmp::Ordering;
use std::collections::HashMap;

use veri_ir::annotation_ir;
use veri_ir::{BoundVar, VIRExpr, VIRTermAnnotation, VIRTermSignature, VIRType};

use cranelift_isle as isle;
use isle::sema::{RuleId, TypeEnv, TypeId};
use veri_annotation::parser_wrapper::AnnotationEnv;

use crate::type_inference::Solution;

#[derive(Clone, Debug)]
pub struct TypeContext<'ctx> {
    // Default bitvector type
    pub ty: VIRType,

    // Pointers to ISLE environments
    typeenv: &'ctx TypeEnv,

    // Isle annotations
    annotation_env: &'ctx AnnotationEnv,

    typesols: &'ctx HashMap<RuleId, Solution>,

    solution: &'ctx Option<Solution>,

    // Map of bound variables to types
    var_types: HashMap<String, VIRType>,
}

impl<'ctx> TypeContext<'ctx> {
    pub fn new(
        typeenv: &'ctx TypeEnv,
        annotation_env: &'ctx AnnotationEnv,
        typesols: &'ctx HashMap<RuleId, Solution>,
        ty: VIRType,
    ) -> Self {
        assert!(ty.is_bv());
        TypeContext {
            typeenv,
            annotation_env,
            typesols,
            solution: &None,
            ty,
            var_types: HashMap::new(),
        }
    }

    fn convert_type(ty: &annotation_ir::Type, query_ty: &VIRType) -> VIRType {
        match ty {
            annotation_ir::Type::Poly(_) => panic!("unexpected after inference"),
            annotation_ir::Type::BitVector => query_ty.clone(),
            annotation_ir::Type::BitVectorWithWidth(w) => VIRType::BitVector(*w),
            annotation_ir::Type::Int => VIRType::Int,
            annotation_ir::Type::Bool => VIRType::Bool,
        }
    }

    fn type_bound_var(&mut self, ruleid: RuleId, term: &str, v: &annotation_ir::BoundVar, query_ty: &VIRType) -> BoundVar {
        let sol = &self.typesols[&ruleid];
        for a in &sol.annotation_infos {
            if (term == a.term) {
                let tyvar = a.var_to_type_var[&v.name];
                let t = &sol.type_var_to_type[&tyvar];
                let ty = Self::convert_type(t, query_ty);
                self.var_types.insert(v.name.clone(), ty.clone());
                return BoundVar {
                    name: v.name.clone(),
                    ty,
                }
            }
        }
        unreachable!("did not find in annotation")
    }

    fn type_expr(&mut self, term: &annotation_ir::Expr, tymap: &HashMap<&String, annotation_ir::Type>) -> VIRExpr {
        let expect_boxed = |e: &annotation_ir::Expr, ctx: &mut Self| {
            let ve = ctx.type_expr(&*e, tymap);
            Box::new(ve)
        };
        let expect_boxed_bool = |e: &annotation_ir::Expr, ctx: &mut Self| {
            let ve = ctx.type_expr(&*e, tymap);
            assert!(ve.ty().is_bool(), "expect_boxed_bool got {:?}", ve);
            Box::new(ve)
        };
        let expect_boxed_bv = |e: &annotation_ir::Expr, ctx: &mut Self| {
            let ve = ctx.type_expr(&*e, tymap);
            assert!(ve.ty().is_bv(), "expect_boxed_bv got {:?}", ve);
            Box::new(ve)
        };
        let expect_boxed_int = |e: &annotation_ir::Expr, ctx: &mut Self| {
            let ve = ctx.type_expr(&*e, tymap);
            assert!(ve.ty().is_int(), "expect_boxed_int got {:?}", ve);
            Box::new(ve)
        };
        match term {
            annotation_ir::Expr::Var(s, t) => VIRExpr::Var(BoundVar {
                name: s.clone(),
                ty: Self::convert_type(&tymap[s], &self.ty)
            }),
            annotation_ir::Expr::Const(c, _) => match c.ty {
                annotation_ir::Type::Int => VIRExpr::Const(VIRType::Int, c.value),
                annotation_ir::Type::BitVector => {
                    VIRExpr::Const(VIRType::BitVector(c.width), c.value)
                }
                _ => todo!("Non-integer constants"),
            },
            annotation_ir::Expr::True(_) => VIRExpr::True,
            annotation_ir::Expr::False(_) => VIRExpr::False,
            annotation_ir::Expr::TyWidth(_) => {
                VIRExpr::Const(VIRType::Int, self.ty.width() as i128)
            }
            annotation_ir::Expr::WidthOf(x, _) => VIRExpr::WidthOf(Box::new(self.type_expr(&*x, tymap))),
            annotation_ir::Expr::Not(e, _) => VIRExpr::Not(expect_boxed_bool(e, self)),
            annotation_ir::Expr::And(x, y, _) => {
                VIRExpr::And(expect_boxed_bool(x, self), expect_boxed_bool(y, self))
            }
            annotation_ir::Expr::Or(x, y, _) => {
                VIRExpr::Or(expect_boxed_bool(x, self), expect_boxed_bool(y, self))
            }
            annotation_ir::Expr::Imp(x, y, _) => {
                VIRExpr::Imp(expect_boxed_bool(x, self), expect_boxed_bool(y, self))
            }
            annotation_ir::Expr::Eq(x, y, _) => {
                let vx = expect_boxed(x, self);
                let vy = expect_boxed(y, self);
                assert_eq!(vx.ty(), vy.ty(), "= {:?} {:?}", vx, vy);
                VIRExpr::Eq(vx, vy)
            }
            annotation_ir::Expr::Lte(x, y, _) => {
                let vx = expect_boxed(x, self);
                let vy = expect_boxed(y, self);
                assert_eq!(vx.ty(), vy.ty());
                VIRExpr::Lte(vx, vy)
            }
            annotation_ir::Expr::BVNeg(x, _) => {
                let vx = expect_boxed_bv(x, self);
                assert!(vx.ty().is_bv());
                VIRExpr::BVNeg(vx.ty().clone(), vx)
            }
            annotation_ir::Expr::BVNot(x, _) => {
                let vx = expect_boxed_bv(x, self);
                assert!(vx.ty().is_bv());
                VIRExpr::BVNot(vx.ty().clone(), vx)
            }
            annotation_ir::Expr::BVAdd(x, y, _) => {
                let vx = expect_boxed_bv(x, self);
                let vy = expect_boxed_bv(y, self);
                assert_eq!(vx.ty(), vy.ty());
                assert!(vx.ty().is_bv());
                VIRExpr::BVAdd(vx.ty().clone(), vx, vy)
            }
            annotation_ir::Expr::BVSub(x, y, _) => {
                let vx = expect_boxed_bv(x, self);
                let vy = expect_boxed_bv(y, self);
                assert_eq!(vx.ty(), vy.ty());
                assert!(vx.ty().is_bv());
                VIRExpr::BVSub(vx.ty().clone(), vx, vy)
            }
            annotation_ir::Expr::BVAnd(x, y, _) => {
                let vx = expect_boxed_bv(x, self);
                let vy = expect_boxed_bv(y, self);
                assert_eq!(vx.ty(), vy.ty());
                assert!(vx.ty().is_bv());
                VIRExpr::BVAnd(vx.ty().clone(), vx, vy)
            }
            annotation_ir::Expr::BVOr(x, y, _) => {
                let vx = expect_boxed_bv(x, self);
                let vy = expect_boxed_bv(y, self);
                assert_eq!(vx.ty(), vy.ty());
                assert!(vx.ty().is_bv());
                VIRExpr::BVOr(vx.ty().clone(), vx, vy)
            }
            annotation_ir::Expr::BVRotl(x, y, _) => {
                let vx = expect_boxed_bv(x, self);
                let vy = expect_boxed_bv(y, self);
                assert_eq!(vx.ty(), vy.ty());
                assert!(vx.ty().is_bv());
                VIRExpr::BVRotl(vx.ty().clone(), vx, vy)
            }
            annotation_ir::Expr::BVShl(x, y, _) => {
                let vx = expect_boxed_bv(x, self);
                let vy = expect_boxed_bv(y, self);
                assert_eq!(vx.ty(), vy.ty());
                assert!(vx.ty().is_bv());
                VIRExpr::BVShl(vx.ty().clone(), vx, vy)
            }
            annotation_ir::Expr::BVShr(x, y, _) => {
                let vx = expect_boxed_bv(x, self);
                let vy = expect_boxed_bv(y, self);
                assert_eq!(vx.ty(), vy.ty());
                assert!(vx.ty().is_bv());
                VIRExpr::BVShr(vx.ty().clone(), vx, vy)
            }
            annotation_ir::Expr::BVZeroExt(i, x, _) => {
                let vx = expect_boxed_bv(x, self);
                assert!(vx.ty().is_bv());
                let new_width = vx.ty().width() + *i;
                VIRExpr::BVZeroExt(VIRType::BitVector(new_width), *i, vx)
            }
            annotation_ir::Expr::BVSignExt(i, x, _) => {
                let vx = expect_boxed_bv(x, self);
                assert!(vx.ty().is_bv());
                let new_width = vx.ty().width() + *i;
                VIRExpr::BVSignExt(VIRType::BitVector(new_width), *i, vx)
            }
            annotation_ir::Expr::BVExtract(l, h, x, _) => {
                let vx = expect_boxed_bv(x, self);
                assert!(vx.ty().is_bv());
                assert!(*h >= *l);
                let new_width = *h - *l + 1;
                VIRExpr::BVExtract(VIRType::BitVector(new_width), *l, *h, vx)
            }
            annotation_ir::Expr::BVConvTo(dest, x, _) => {
                let vx = expect_boxed_bv(x, self);
                assert!(vx.ty().is_bv() || vx.ty().is_int());
                assert!(self.ty.is_bv());
                let width = match **dest {
                    annotation_ir::Width::Const(c) => c,
                    annotation_ir::Width::RegWidth => self.ty.width(),
                };
                let new_ty = VIRType::BitVector(width);
                match vx.ty() {
                    VIRType::BitVector(w) => {
                        dbg!(width);
                        dbg!(w);
                        let width_diff = width - *w;
                        match width_diff.cmp(&0) {
                            Ordering::Less => VIRExpr::BVExtract(new_ty, 0, width - 1, vx),
                            Ordering::Greater => VIRExpr::BVZeroExt(new_ty, width_diff, vx),
                            Ordering::Equal => *vx,
                        }
                    }
                    _ => unreachable!("{:?}", vx.ty()),
                }
            }
            annotation_ir::Expr::BVConvFrom(src, x, _) => {
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
            annotation_ir::Expr::BVIntToBv(width, x, _) => {
                let width = expect_boxed_bv(width, self);
                let vx = expect_boxed_int(x, self);
                VIRExpr::BVIntToBV(width.ty().clone(), vx)
            }
        }
    }

    pub fn typed_isle_annotation_for_term(
        &mut self,
        ruleid: RuleId,
        term: &str,
        _subterm_typeids: Vec<TypeId>,
        query_ty: &VIRType,
    ) -> Option<VIRTermAnnotation> {
        let initial_term = self.annotation_env.get_annotation_for_term(term);
        let mut tymap = HashMap::new();
        let sol = &self.typesols[&ruleid];
        for a in &sol.annotation_infos {
            if term == a.term {
                for (var, type_var) in &a.var_to_type_var {
                    tymap.insert(var, sol.type_var_to_type[&type_var].clone());
                }
            }
        }
        initial_term.map(|a| {
            VIRTermAnnotation::new(
                VIRTermSignature {
                    args: a
                        .sig()
                        .args
                        .iter()
                        .enumerate()
                        .map(|(i, b)| self.type_bound_var(ruleid, term, b, &query_ty))
                        .collect(),
                    ret: self.type_bound_var(ruleid, term, &a.sig().ret, &query_ty),
                },
                a.assertions().iter().map(|e| self.type_expr(e, &tymap)).collect(),
            )
        })
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
            "Imm64" => VIRType::BitVector(64),
            "ImmShift" => VIRType::BitVector(6),
            "ImmLogic" => VIRType::BitVector(12),
            "u64" => VIRType::BitVector(64),
            "u8" => VIRType::BitVector(8),
            "MoveWideConst" => VIRType::BitVector(16),
            "OperandSize" => self.ty.clone(),
            // TODO: should probably update this logic to use an actual
            // register width for some of these
            "Reg" | "Inst" | "Value" | "ValueRegs" | "InstructionData" => self.ty.clone(),

            // For now, hard code errors for these types that we later want to
            // explicitly mark as unsafe.
            "Opcode" => unreachable!(),
            "ALUOp" => unreachable!(),
            "ValueArray2" => unreachable!(),
            _ => unimplemented!("ty: {}", clif_name),
        }
    }
}
