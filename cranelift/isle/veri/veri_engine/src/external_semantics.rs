/// Convert our internal Verification IR to an external SMT AST and pass
/// queries to that solver.
///
/// Right now, this uses the rsmt2 crate.
use crate::interp::AssumptionContext;
use rsmt2::Solver;
use veri_ir::{BoundVar, Counterexample, VIRExpr, VIRType, VerificationResult, Function};

pub fn vir_to_rsmt2_constant_ty(ty: VIRType) -> Option<String> {
    match ty {
        VIRType::BitVector(width) => Some(format!("(_ BitVec {})", width)),
        VIRType::BitVectorList(len, width) => Some(format!("(_ BitVec {})", len*width)),
        VIRType::IsleType => Some("Int".to_string()),
        VIRType::Bool | VIRType::Function => None,
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
    let ec = e.clone();
    match e {
        VIRExpr::Const(ty, i) => match ty {
            VIRType::BitVector(width) => format!("(_ bv{} {})", i, width),
            VIRType::IsleType => i.to_string(),
            VIRType::Bool => (if i == 0 { "false" } else { "true" }).to_string(),
            VIRType::Function => unimplemented!(),
            VIRType::BitVectorList(_length, _width) => unimplemented!(),
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
        VIRExpr::FunctionApplication(_, func, arg_list) => match *func {
            VIRExpr::Function(Function{name, ret, args}) => {
                unary(&name, arg_list)
            }
            _ => unreachable!("Unsupported function structure: {:?}", ec),
        },
        VIRExpr::List(_, args) => {
            // Implement lists as concatenations of vectors
            // For now, assume length 2
            match &args[..]  {
                [x, y] => 
                format!(
                    "(concat {} {})",
                    vir_expr_to_rsmt2_str(x.clone()),
                    vir_expr_to_rsmt2_str(y.clone())
                ),
                _ => unimplemented!("unimplemented arg length")
            }
        }
        _ => unreachable!("Unexpected expr {:?}", ec),
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
        if let Some(var_ty) = vir_to_rsmt2_constant_ty(v.ty) {
            println!("\t{} : {:?}", v.name, v.ty);
            solver.declare_const(v.name, var_ty).unwrap();
        } 
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
            VerificationResult::Failure(Counterexample {})
        }
        Ok(false) => {
            println!("Verification succeeded");
            VerificationResult::Success
        }
        Err(err) => {
            unreachable!("Error! {:?}", err);
        }
    }
}
