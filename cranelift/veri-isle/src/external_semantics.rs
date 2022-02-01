//! External definitions need to specify both their assumptions and what they
//! produce.
//!
//! Right now, this uses the rsmt2 crate's datatypes.

use crate::assumptions::AssumptionContext;
use crate::smt_ast::BVExpr;
use crate::types::SMTType;
use rsmt2::Solver;

impl SMTType {
    pub fn to_rsmt2_str(self) -> String {
        match self {
            SMTType::BitVector(width) => format!("(_ BitVec {})", width),
        }
    }
}

pub fn bv_expr_to_rsmt2_str(e: BVExpr) -> String {
    match e {
        BVExpr::Const(i) => i.to_string(),
        BVExpr::Var(s) => s,
        BVExpr::BVNeg(x) => format!("(bvneg {})", bv_expr_to_rsmt2_str(*x)),
        BVExpr::BVNot(x) => format!("(bvnot {})", bv_expr_to_rsmt2_str(*x)),
        BVExpr::BVAdd(x, y) => format!(
            "(bvadd {} {})",
            bv_expr_to_rsmt2_str(*x),
            bv_expr_to_rsmt2_str(*y)
        ),
        BVExpr::BVSub(x, y) => format!(
            "(bvsub {} {})",
            bv_expr_to_rsmt2_str(*x),
            bv_expr_to_rsmt2_str(*y)
        ),
    }
}

/// Overall query: (not (=> <assumptions> (= <LHS> <RHS>)))
pub fn run_solver(actx: AssumptionContext, lhs: BVExpr, rhs: BVExpr, ty: SMTType) {
    let mut solver = Solver::default_z3(()).unwrap();
    let arg_ty = ty.to_rsmt2_str();

    for v in actx.quantified_vars {
        solver.declare_const(v.name, v.ty.to_rsmt2_str());
    }

    let lhs_s = bv_expr_to_rsmt2_str(lhs);
    let rhs_s = bv_expr_to_rsmt2_str(rhs);

    solver.assert(format!("(not (=> {} (= {} {})))", "true", lhs_s, rhs_s));

    let is_sat = solver.check_sat();
    dbg!(is_sat);
}
