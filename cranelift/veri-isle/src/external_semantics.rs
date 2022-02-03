//! External definitions need to specify both their assumptions and what they
//! produce.
//!
//! Right now, this uses the rsmt2 crate's datatypes.

use crate::interp_lhs::AssumptionContext;
use crate::smt_ast::{BVExpr, BoolExpr, SMTType};
use rsmt2::Solver;

impl SMTType {
    pub fn to_rsmt2_str(self) -> String {
        match self {
            SMTType::BitVector(width) => format!("(_ BitVec {})", width),
            SMTType::Bool => unreachable!("{:?}", self)
        }
    }
}

pub fn bv_expr_to_rsmt2_str(e: BVExpr) -> String {
    let unary = |op, x: Box<BVExpr>| format!("({} {})", op, bv_expr_to_rsmt2_str(*x));
    let binary = |op, x: Box<BVExpr>, y: Box<BVExpr>| {
        format!(
            "({} {} {})",
            op,
            bv_expr_to_rsmt2_str(*x),
            bv_expr_to_rsmt2_str(*y)
        )
    };

    match e {
        BVExpr::Const(ty, i) => format!("(_ bv{} {})", i, ty.width()),
        BVExpr::Var(_, s) => s,
        BVExpr::BVNeg(_, x) => unary("bvneg", x),
        BVExpr::BVNot(_, x) => unary("bvnot", x),
        BVExpr::BVAdd(_, x, y) => binary("bvadd", x, y),
        BVExpr::BVSub(_, x, y) => binary("bvsub", x, y),
        BVExpr::BVAnd(_, x, y) => binary("bvand", x, y),
    }
}

pub fn bool_expr_to_rsmt2_str(e: BoolExpr, ty: SMTType) -> String {
    let unary = |op, x: Box<BoolExpr>| format!("({} {})", op, bool_expr_to_rsmt2_str(*x, ty));
    let binary = |op, x: Box<BoolExpr>, y: Box<BoolExpr>| {
        format!(
            "({} {} {})",
            op,
            bool_expr_to_rsmt2_str(*x, ty),
            bool_expr_to_rsmt2_str(*y, ty)
        )
    };
    match e {
        BoolExpr::True => "true".to_string(),
        BoolExpr::False => "false".to_string(),
        BoolExpr::Not(x) => unary("not", x),
        BoolExpr::And(x, y) => binary("and", x, y),
        BoolExpr::Or(x, y) => binary("or", x, y),
        BoolExpr::Imp(x, y) => binary("=>", x, y),
        BoolExpr::Eq(x, y) => format!(
            "(= {} {})",
            bv_expr_to_rsmt2_str(*x),
            bv_expr_to_rsmt2_str(*y)
        ),
    }
}

/// Overall query:
/// <declare vars>
/// (not (=> <assumptions> (= <LHS> <RHS>))))))
///
pub fn run_solver(actx: AssumptionContext, lhs: BVExpr, rhs: BVExpr, ty: SMTType) {
    let mut solver = Solver::default_z3(()).unwrap();
    let arg_ty = ty.to_rsmt2_str();

    for v in actx.quantified_vars {
        println!("Declaring constant {} of type {:?}", v.name, v.ty);
        solver.declare_const(v.name, v.ty.to_rsmt2_str());
    }

    let assumptions: Vec<String> = actx
        .assumptions
        .iter()
        .map(|a| bool_expr_to_rsmt2_str(a.assume.clone(), ty))
        .collect();
    let assumption_str = format!("(and {})", assumptions.join(" "));

    let lhs_s = bv_expr_to_rsmt2_str(lhs);
    let rhs_s = bv_expr_to_rsmt2_str(rhs);

    let query = format!("(not (=> {} (= {} {})))", assumption_str, lhs_s, rhs_s);
    println!("Running query: {}", query);
    solver.assert(query).unwrap();

    match solver.check_sat() {
        Ok(true) => println!("Verification failed"),
        Ok(false) => println!("Verification succeeded"),
        Err(err) => {
            println!("Error!");
            dbg!(err);
        }
    }
}
