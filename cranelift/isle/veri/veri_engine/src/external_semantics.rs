/// Convert our internal Verification IR to an external SMT AST and pass
/// queries to that solver.
///
/// Right now, this uses the rsmt2 crate.
use crate::interp::AssumptionContext;
use std::collections::HashSet;
use rsmt2::Solver;
use veri_ir::{Counterexample, VIRExpr, VIRType, VerificationResult};

pub fn vir_to_rsmt2_constant_ty(ty: &VIRType) -> String {
    match ty {
        VIRType::BitVector(width) => format!("(_ BitVec {})", width),
        VIRType::BitVectorList(len, width) => format!("(_ BitVec {})", len * width),
        VIRType::IsleType => "Int".to_string(),
        VIRType::Bool | VIRType::Function(..) => unreachable!(),
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
            VIRType::Function(..) => unimplemented!(),
            VIRType::BitVectorList(_length, _width) => unimplemented!(),
        },
        VIRExpr::Var(bound_var) => bound_var.name,
        VIRExpr::True => "true".to_string(),
        VIRExpr::False => "false".to_string(),
        VIRExpr::Not(x) => unary("not", x),
        VIRExpr::And(x, y) => binary("and", x, y),
        VIRExpr::Or(x, y) => binary("or", x, y),
        VIRExpr::Imp(x, y) => binary("=>", x, y),
        // If the assertion is an equality on function types, we need quantification
        VIRExpr::Eq(x, y) if x.ty().is_function() => {
            let x_str = vir_expr_to_rsmt2_str(*x.clone());
            let y_str = vir_expr_to_rsmt2_str(*y);
            let args = x
                .ty()
                .function_arg_types()
                .iter()
                .enumerate()
                .map(|(i, t)| format!("(x{} {})", i, vir_to_rsmt2_constant_ty(t)))
                .collect::<Vec<String>>()
                .join(" ");
            let arg_names = x
                .ty()
                .function_arg_types()
                .iter()
                .enumerate()
                .map(|(i, _)| format!("x{}", i,))
                .collect::<Vec<String>>()
                .join(" ");
            format!(
                "(forall ({}) (= ({} {}) ({} {})))",
                args, x_str, arg_names, y_str, arg_names
            )
        }
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
        VIRExpr::FunctionApplication(app) => {
            let func_name = vir_expr_to_rsmt2_str(*app.func);
            let args: Vec<String> = app
                .args
                .iter()
                .map(|a| vir_expr_to_rsmt2_str(a.clone()))
                .collect();
            format!("({} {})", func_name, args.join(" "))
        }
        VIRExpr::Function(func) => func.name,
        VIRExpr::List(_, args) => {
            // Implement lists as concatenations of bitvectors
            // For now, assume length 2
            match &args[..] {
                [x, y] => format!(
                    "(concat {} {})",
                    vir_expr_to_rsmt2_str(x.clone()),
                    vir_expr_to_rsmt2_str(y.clone())
                ),
                _ => unimplemented!("unimplemented arg length"),
            }
        }
        VIRExpr::GetElement(ty, ls, i) => {
            // List are concatenations of bitvectors, so extract to
            // get the element
            let start = i * ty.width();
            let end = start + ty.width() - 1;
            vir_expr_to_rsmt2_str(VIRExpr::BVExtract(ty, start, end, ls))
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

fn declare_uninterp_functions(expr: VIRExpr, solver: &mut Solver<()>) {
    let mut fns = HashSet::new();
    let mut f = |e: &VIRExpr| {
        if let VIRExpr::Function(func) = e {
            if fns.contains(&func.name) {
                // Skip functions we've already seen (the solver will catch
                // mismatched types)
                return;
            } else {
                fns.insert(func.name.clone())
            };
            let arg_tys: Vec<String> = func
                .args
                .iter()
                .map(|a| vir_to_rsmt2_constant_ty(&a.ty))
                .collect();
            solver
                .declare_fun(
                    func.name.clone(),
                    arg_tys,
                    vir_to_rsmt2_constant_ty(&func.ty.function_ret_type()),
                )
                .unwrap();

            println!("\t{} : {:?}", func.name, func.ty);

            let args = func
                .args
                .iter()
                .map(|var| format!("({} {})", var.name, vir_to_rsmt2_constant_ty(&var.ty)))
                .collect::<Vec<String>>()
                .join(" ");
            let arg_names = func
                .args
                .iter()
                .map(|v| v.name.to_string())
                .collect::<Vec<String>>()
                .join(" ");
            let defn = format!(
                "(forall ({}) (= ({} {}) {}))",
                args,
                func.name,
                arg_names,
                vir_expr_to_rsmt2_str(*func.body.clone())
            );
            solver.assert(defn).unwrap();
        }
    };
    expr.for_each_subexpr(&mut f);
}

/// Overall query:
/// <declare vars>
/// (not (=> <assumptions> (= <LHS> <RHS>))))))
pub fn run_solver(
    actx: AssumptionContext,
    lhs: VIRExpr,
    rhs: VIRExpr,
    _ty: &VIRType,
) -> VerificationResult {
    let mut solver = Solver::default_z3(()).unwrap();
    println!("Declaring constants:");
    for v in actx.quantified_vars {
        let name = v.name.clone();
        let ty = &v.ty;
        match ty.clone() {
            VIRType::Function(args, ret) => {
                println!("\tFUNCTION {} : {:?}", name, ty);
                let arg_tys: Vec<String> =
                    args.iter().map(|a| vir_to_rsmt2_constant_ty(a)).collect();
                solver
                    .declare_fun(name, arg_tys, vir_to_rsmt2_constant_ty(&*ret))
                    .unwrap();
            }
            _ => {
                let var_ty = vir_to_rsmt2_constant_ty(ty);
                println!("\t{} : {:?}", name, ty);
                solver.declare_const(name, var_ty).unwrap();
            }
        }
    }

    println!("Declaring uninterpreted functions:");
    for a in &actx.assumptions {
        declare_uninterp_functions(a.assume().clone(), &mut solver);
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

    // Check whether the assumptions are possible
    if !check_assumptions_feasibility(&mut solver, assumption_str.clone()) {
        println!("Rule not applicable as written, skipping full query");
        return VerificationResult::InapplicableRule;
    }

    // Correctness query
    let lhs_s = vir_expr_to_rsmt2_str(lhs);
    let rhs_s = vir_expr_to_rsmt2_str(rhs);

    let query = format!("(not (=> {} (= {} {})))", assumption_str, lhs_s, rhs_s);
    println!("Running query:\n\t{}\n", query);
    solver.assert(query).unwrap();

    match solver.check_sat() {
        Ok(true) => {
            println!("Verification failed");
            let model = solver.get_model().unwrap();
            dbg!(model);
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
