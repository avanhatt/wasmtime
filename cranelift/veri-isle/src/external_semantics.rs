//! External definitions need to specify both their assumptions and what they
//! produce.
//!
//! Right now, this uses the rsmt2 crate's datatypes.

use crate::assumptions::AssumptionContext;
use crate::smt_ast::{BVExpr, BoolExpr};
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
        BVExpr::Const(i, s) => format!("(_ bv{} {})", i, s),
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

pub fn bool_expr_to_rsmt2_str(e: BoolExpr) -> String {
    match e {
        BoolExpr::True => "true".to_string(),
        BoolExpr::False => "false".to_string(),
        BoolExpr::Not(x) => format!("(not {})", bool_expr_to_rsmt2_str(*x)),
        BoolExpr::And(x, y) => format!(
            "(and {} {})",
            bool_expr_to_rsmt2_str(*x),
            bool_expr_to_rsmt2_str(*y)
        ),
        BoolExpr::Or(x, y) => format!(
            "(or {} {})",
            bool_expr_to_rsmt2_str(*x),
            bool_expr_to_rsmt2_str(*y)
        ),
        BoolExpr::Imp(x, y) => format!(
            "(=> {} {})",
            bool_expr_to_rsmt2_str(*x),
            bool_expr_to_rsmt2_str(*y)
        ),
        BoolExpr::Eq(x, y) => format!(
            "(= {} {})",
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

    let assumptions : Vec<String> = actx.assumptions.iter().map(|a| {
        bool_expr_to_rsmt2_str(a.assume.clone())
    }).collect();
    let assumption_str = format!("(and {})", assumptions.join(" "));

    let lhs_s = bv_expr_to_rsmt2_str(lhs);
    let rhs_s = bv_expr_to_rsmt2_str(rhs);


    let query = format!("(not (=> {} (= {} {})))", assumption_str, lhs_s, rhs_s);
    println!("Running query: {}", query);
    solver.assert(query);

    match solver.check_sat() {
        Ok(true) => println!("Verification failed"), 
        Ok(false) => println!("Verification succeeded"), 
        Err(err) => { println!("Error!"); dbg!(err); },
    }

}
