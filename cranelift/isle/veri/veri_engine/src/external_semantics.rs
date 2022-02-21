//! Convert our internal SMT AST to an external one and pass queries to that
//! solver.
//!
//! Right now, this uses the rsmt2 crate.

use crate::interp_lhs::AssumptionContext;
use rsmt2::Solver;
use veri_ir::{BVExpr, BoolExpr, VIRType};

pub fn vir_to_rsmt2_str(ty: VIRType) -> String {
    match ty {
        VIRType::BitVector(width) => format!("(_ BitVec {})", width),
        VIRType::Bool => unreachable!("{:?}", ty),
        VIRType::IsleType => "Int".to_string(),
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
    let ext = |op, i, x: Box<BVExpr>| format!("((_ {} {}) {})", op, i, bv_expr_to_rsmt2_str(*x));

    match e {
        BVExpr::Const(ty, i) => format!("(_ bv{} {})", i, ty.width()),
        BVExpr::Var(bound_var) => bound_var.name,
        BVExpr::BVNeg(_, x) => unary("bvneg", x),
        BVExpr::BVNot(_, x) => unary("bvnot", x),
        BVExpr::BVAdd(_, x, y) => binary("bvadd", x, y),
        BVExpr::BVSub(_, x, y) => binary("bvsub", x, y),
        BVExpr::BVAnd(_, x, y) => binary("bvand", x, y),
        BVExpr::BVZeroExt(_, i, x) => ext("zero_extend", i, x),
        BVExpr::BVSignExt(_, i, x) => ext("sign_extend", i, x),
        BVExpr::BVExtract(_, l, h, x) => {
            format!("((_ extract {} {}) {})", h, l, bv_expr_to_rsmt2_str(*x))
        }
    }
}

pub fn bool_expr_to_rsmt2_str(e: BoolExpr, ty: VIRType) -> String {
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

// Checks whether the assumption list is always false
fn check_assumptions_feasibility<Parser>(solver: &mut Solver<Parser>, assumptions: String) -> bool {
    solver.push(1).unwrap();
    solver.assert(assumptions).unwrap();
    let res = match solver.check_sat() {
        Ok(true) => {
            println!("Assertion list is feasible");
            true
        }
        Ok(false) => {
            println!("Assertion list is infeasible!");
            false
        }
        Err(err) => {
            unreachable!("Error! {:?}", err);
        }
    };
    solver.pop(1).unwrap();
    res
}

/// Overall query:
/// <declare vars>
/// (not (=> <assumptions> (= <LHS> <RHS>))))))
///
pub fn run_solver(actx: AssumptionContext, lhs: BVExpr, rhs: BVExpr, ty: VIRType) {
    let mut solver = Solver::default_z3(()).unwrap();
    println!("Declaring constants:");
    for v in actx.quantified_vars {
        println!("\t{} : {:?}", v.name, v.ty);
        solver
            .declare_const(v.name, vir_to_rsmt2_str(v.ty))
            .unwrap();
    }

    println!("Adding assumptions:");
    let assumptions: Vec<String> = actx
        .assumptions
        .iter()
        .map(|a| {
            let p = bool_expr_to_rsmt2_str(a.assume.clone(), ty);
            println!("\t{}", p);
            p
        })
        .collect();
    let assumption_str = format!("(and {})", assumptions.join(" "));

    let lhs_s = bv_expr_to_rsmt2_str(lhs);
    let rhs_s = bv_expr_to_rsmt2_str(rhs);

    // Check whether the assumptions are possible
    if !check_assumptions_feasibility(&mut solver, assumption_str.clone()) {
        println!("Rule not applicable as written, skipping full query");
        return;
    }

    let query = format!("(not (=> {} (= {} {})))", assumption_str, lhs_s, rhs_s);
    println!("Running query:\n\t{}\n", query);
    solver.assert(query).unwrap();

    match solver.check_sat() {
        Ok(true) => println!("Verification failed"),
        Ok(false) => println!("Verification succeeded"),
        Err(err) => {
            unreachable!("Error! {:?}", err);
        }
    }
}
