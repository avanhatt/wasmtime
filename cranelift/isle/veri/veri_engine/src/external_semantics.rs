/// Convert our internal Verification IR to an external SMT AST and pass
/// queries to that solver.
///
/// Right now, this uses the rsmt2 crate.
use crate::interp::AssumptionContext;
use rsmt2::Solver;
use veri_ir::{Counterexample, VIRExpr, VIRType, VerificationResult};

pub fn vir_to_rsmt2_str(ty: VIRType) -> String {
    match ty {
        VIRType::BitVector(width) => format!("(_ BitVec {})", width),
        VIRType::Bool => unreachable!("{:?}", ty),
        VIRType::IsleType => "Int".to_string(),
    }
}

pub fn vir_expr_to_rsmt2_str(e: VIRExpr) -> String {
    let unary = |op, x: Box<VIRExpr>| format!("({} {})", op, vir_expr_to_rsmt2_str(*x));
    let binary = |op, x: Box<VIRExpr>, y: Box<VIRExpr>| {
        format!(
            "({} {} {})",
            op,
            vir_expr_to_rsmt2_str(*x),
            vir_expr_to_rsmt2_str(*y)
        )
    };
    let ext = |op, i, x: Box<VIRExpr>| format!("((_ {} {}) {})", op, i, vir_expr_to_rsmt2_str(*x));

    match e {
        VIRExpr::Const(ty, i) => match ty {
            VIRType::BitVector(width) => format!("(_ bv{} {})", i, width),
            VIRType::IsleType => i.to_string(),
            VIRType::Bool => (if i == 0 { "false" } else { "true" }).to_string(),
        },
        VIRExpr::Var(bound_var) => bound_var.name,
        VIRExpr::True => "true".to_string(),
        VIRExpr::False => "false".to_string(),
        VIRExpr::Not(x) => unary("not", x),
        VIRExpr::And(x, y) => binary("and", x, y),
        VIRExpr::Or(x, y) => binary("or", x, y),
        VIRExpr::Imp(x, y) => binary("=>", x, y),
        VIRExpr::Eq(x, y) => binary("=", x, y),
        VIRExpr::Lte(x, y) => binary("<=", x, y),
        VIRExpr::BVNeg(_, x) => unary("bvneg", x),
        VIRExpr::BVNot(_, x) => unary("bvnot", x),
        VIRExpr::BVAdd(_, x, y) => binary("bvadd", x, y),
        VIRExpr::BVSub(_, x, y) => binary("bvsub", x, y),
        VIRExpr::BVAnd(_, x, y) => binary("bvand", x, y),
        VIRExpr::BVZeroExt(_, i, x) => ext("zero_extend", i, x),
        VIRExpr::BVSignExt(_, i, x) => ext("sign_extend", i, x),
        VIRExpr::BVExtract(_, l, h, x) => {
            format!("((_ extract {} {}) {})", h, l, vir_expr_to_rsmt2_str(*x))
        }
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
pub fn run_solver(
    actx: AssumptionContext,
    lhs: VIRExpr,
    rhs: VIRExpr,
    _ty: VIRType,
) -> VerificationResult {
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
            let p = vir_expr_to_rsmt2_str(a.assume().clone());
            println!("\t{}", p);
            p
        })
        .collect();
    let assumption_str = format!("(and {})", assumptions.join(" "));

    let lhs_s = vir_expr_to_rsmt2_str(lhs);
    let rhs_s = vir_expr_to_rsmt2_str(rhs);

    // Check whether the assumptions are possible
    if !check_assumptions_feasibility(&mut solver, assumption_str.clone()) {
        println!("Rule not applicable as written, skipping full query");
        return VerificationResult::InapplicableRule;
    }

    let query = format!("(not (=> {} (= {} {})))", assumption_str, lhs_s, rhs_s);
    println!("Running query:\n\t{}\n", query);
    solver.assert(query).unwrap();

    match solver.check_sat() {
        Ok(true) => {
            println!("Verification failed");
            return VerificationResult::Failure(Counterexample {});
        }
        Ok(false) => {
            println!("Verification succeeded");
            return VerificationResult::Success;
        }
        Err(err) => {
            unreachable!("Error! {:?}", err);
        }
    }
}
