use crate::interp_lhs::AssumptionContext;
use crate::smt_ast::{BVExpr, BoolExpr};
use crate::types::SMTType;

use cranelift_isle as isle;
use isle::sema::{Expr, Pattern, Term, TermArgPattern, TermEnv, TypeEnv, VarId};

pub struct InterpContext {}

impl InterpContext {
    fn interp_bv_expr(
        &mut self,
        bvexpr: &Expr,
        actx: &AssumptionContext,
        termenv: &TermEnv,
        typeenv: &TypeEnv,
        ty: SMTType,
    ) -> BVExpr {
        match bvexpr {
            Expr::Term(tyid, termid, subterms) => {
                let term = &termenv.terms[termid.index()];
                let term_name = &typeenv.syms[term.name.index()];
                // Inline for now, needs to be extracted
                match term_name.as_str() {
                    // No op for now
                    "value_reg" | "put_in_reg" => {
                        assert_eq!(subterms.len(), 1);
                        return self.interp_bv_expr(&subterms[0], actx, termenv, typeenv, ty);
                    }
                    "add" => {
                        // Ignore the type arg for now
                        assert_eq!(subterms.len(), 3);
                        return BVExpr::BVAdd(
                            Box::new(self.interp_bv_expr(&subterms[1], actx, termenv, typeenv, ty)),
                            Box::new(self.interp_bv_expr(&subterms[2], actx, termenv, typeenv, ty)),
                        );
                    }
                    "sub_imm" => {
                        // Ignore the type arg for now
                        assert_eq!(subterms.len(), 3);
                        return BVExpr::BVSub(
                            Box::new(self.interp_bv_expr(&subterms[1], actx, termenv, typeenv, ty)),
                            Box::new(self.interp_bv_expr(&subterms[2], actx, termenv, typeenv, ty)),
                        );
                    }
                    _ => unimplemented!("{}", term_name),
                }
            }
            Expr::Var(tyid, varid) => BVExpr::Var(actx.var_map.get(varid).unwrap().name.clone()),
            _ => unimplemented!(),
        }
    }

    pub fn interp_rhs(
        &mut self,
        rhs: &Expr,
        actx: &AssumptionContext,
        termenv: &TermEnv,
        typeenv: &TypeEnv,
        ty: SMTType,
    ) -> BVExpr {
        self.interp_bv_expr(rhs, actx, termenv, typeenv, ty)
    }
}
