/// Convert our internal Verification IR to an external SMT AST and pass
/// queries to that solver.
///
/// Right now, this uses the rsmt2 crate.
use rsmt2::Solver;
use veri_ir::{Counterexample, Expr, RulePath, Type, VerificationResult};

const BITWIDTH: usize = 64;

struct Query {
    bv_names: Vec<String>,
    bvwidth_names: Vec<String>,
    bv_decl_idx: usize,
}

pub fn vir_to_rsmt2_constant_ty(ty: &Type) -> String {
    match ty {
        Type::BitVector => format!("(_ BitVec {})", BITWIDTH),
        Type::Int => "Int".to_string(),
        Type::Bool => unreachable!(),
    }
}

pub fn vir_expr_to_rsmt2_str(e: Expr) -> String {
    todo!()
    // let unary = |op, x: Box<Expr>| format!("({} {})", op, vir_expr_to_rsmt2_str(*x));
    // let binary = |op, x: Box<Expr>, y: Box<Expr>| {
    //     format!(
    //         "({} {} {})",
    //         op,
    //         vir_expr_to_rsmt2_str(*x),
    //         vir_expr_to_rsmt2_str(*y)
    //     )
    // };
    // let ext = |op, i, x: Box<Expr>| format!("((_ {} {}) {})", op, i, vir_expr_to_rsmt2_str(*x));
    // match e {
    //     Expr::Const(ty, i) => match ty {
    //         VIRType::BitVector(width) => format!("(_ bv{} {})", i, BITWIDTH),
    //         VIRType::Int => i.to_string(),
    //         VIRType::Bool => (if i == 0 { "false" } else { "true" }).to_string(),
    //     },
    //     Expr::Var(bound_var) => bound_var.name,
    //     Expr::True => "true".to_string(),
    //     Expr::False => "false".to_string(),
    //     Expr::Not(x) => unary("not", x),
    //     Expr::And(x, y) => binary("and", x, y),
    //     Expr::Or(x, y) => binary("or", x, y),
    //     Expr::Imp(x, y) => binary("=>", x, y),
    //     Expr::Eq(x, y) => binary("=", x, y),
    //     Expr::Lte(x, y) => binary("<=", x, y),
    //     Expr::BVNeg(_, x) => unary("bvneg", x),
    //     Expr::BVNot(_, x) => unary("bvnot", x),
    //     Expr::BVAdd(_, x, y) => binary("bvadd", x, y),
    //     Expr::BVSub(_, x, y) => binary("bvsub", x, y),
    //     Expr::BVAnd(_, x, y) => binary("bvand", x, y),
    //     Expr::BVOr(_, x, y) => binary("bvor", x, y),
    //     Expr::BVRotl(ty, x, i) => {
    //         // SMT bitvector rotate_left requires that the rotate amount be
    //         // statically specified. Instead, to use a dynamic amount, desugar
    //         // to shifts and bit arithmetic.
    //         format!(
    //             "(bvor (bvshl {x} {i}) (bvlshr {x} (bvsub {width} {i})))",
    //             x = vir_expr_to_rsmt2_str(*x),
    //             i = vir_expr_to_rsmt2_str(*i.clone()),
    //             width = format!("(_ bv{} {})", ty.width(), BITWIDTH)
    //         )
    //     }
    //     Expr::BVShl(_, x, y) => binary("bvshl", x, y),
    //     Expr::BVShr(_, x, y) => binary("bvlshr", x, y),
    //     Expr::BVZeroExt(_, i, x) =>
    //     // ext("zero_extend", i, x),
    //     {
    //         format!("{}", vir_expr_to_rsmt2_str(*x))
    //     }

    //     Expr::BVSignExt(_, i, x) => ext("sign_extend", i, x),
    //     Expr::BVExtract(_, l, h, x) => {
    //         // format!("((_ extract {} {}) {})", h, l, vir_expr_to_rsmt2_str(*x))
    //         format!("{}", vir_expr_to_rsmt2_str(*x))
    //     }
    //     Expr::BVIntToBV(ty, x) => {
    //         format!("((_ int2bv {}) {})", BITWIDTH, vir_expr_to_rsmt2_str(*x))
    //     }
    //     Expr::UndefinedTerm(term) => term.ret.name,
    //     Expr::WidthOf(x) => x.ty().width().to_string(),
    //}
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

//

/// Overall query:
/// <declare vars>
/// (not (=> <assumptions> (= <LHS> <RHS>))))))
pub fn run_solver_single_rule(rule_sem: veri_ir::RuleSemantics, _ty: &Type) -> VerificationResult {
    let mut solver = Solver::default_z3(()).unwrap();
    println!("Declaring constants:");
    for v in rule_sem.quantified_vars {
        todo!()
        // let name = v.name.clone();
        // let ty = &v.ty;
        // match ty.clone() {
        //     _ => {
        //         let var_ty = vir_to_rsmt2_constant_ty(ty);
        //         println!("\t{} : {:?}", name, ty);
        //         solver.declare_const(name, var_ty).unwrap();
        //     }
        // }
    }

    // println!("Declaring uninterpreted functions:");
    // for a in &rule_sem.assumptions {
    //     declare_uninterp_functions(a.clone(), &mut solver);
    // }

    println!("Adding assumptions:");
    let assumptions: Vec<String> = rule_sem
        .assumptions
        .iter()
        .map(|a| {
            let p = vir_expr_to_rsmt2_str(a.clone());
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
    let lhs_s = vir_expr_to_rsmt2_str(rule_sem.lhs);
    let rhs_s = vir_expr_to_rsmt2_str(rule_sem.rhs);

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

/// Overall query:
/// <declare vars>
/// (not (=> (and
///             <all rules' assumptions>
///             <between rule assumptions>
///             <all but first rule's <LHS> = <RHS>>)
///          (= <first rule LHS> <first rule RHS>))))))
pub fn run_solver_rule_path(rule_path: RulePath) -> VerificationResult {
    let mut solver = Solver::default_z3(()).unwrap();

    let mut assumptions: Vec<String> = vec![];
    let mut between_rule_assumptions: Vec<String> = vec![];

    for (v1, v2) in rule_path.undefined_term_pairs {
        let equality = format!("(= {} {})", v1.ret.name, v2.ret.name);
        between_rule_assumptions.push(equality);
        assert_eq!(v1.args.len(), v2.args.len());
        for (a1, a2) in v1.args.iter().zip(&v2.args) {
            let a1_s = vir_expr_to_rsmt2_str(a1.clone());
            let a2_s = vir_expr_to_rsmt2_str(a2.clone());
            let equality = format!("(= {} {})", a1_s, a2_s);
            between_rule_assumptions.push(equality)
        }
    }
    for rule_sem in &rule_path.rules {
        println!("Declaring constants:");
        for v in &rule_sem.quantified_vars {
            let name = v.name.clone();
            todo!()
            // match &v.ty {
            //     VIRType::BitVector => {
            //         let var_ty = vir_to_rsmt2_constant_ty(&v.ty);
            //         println!("\t{} : {:?}", name, &var_ty);
            //         solver.declare_const(name, var_ty).unwrap();
            //     }
            //     _ => {
            //         let var_ty = vir_to_rsmt2_constant_ty(&v.ty);
            //         println!("\t{} : {:?}", name);
            //         solver.declare_const(name, var_ty).unwrap();
            //     }
            // }
        }

        println!("Adding assumptions:");
        for a in &rule_sem.assumptions {
            let p = vir_expr_to_rsmt2_str(a.clone());
            println!("\t{}", p);
            assumptions.push(p)
        }

        let assumption_str = format!("(and {})", assumptions.join(" "));

        // Check whether the assumptions are possible
        if !check_assumptions_feasibility(&mut solver, assumption_str.clone()) {
            println!("Rule not applicable as written for rule assumptions, skipping full query");
            return VerificationResult::InapplicableRule;
        }
    }

    println!("Adding assumptions on relationship between rules");
    assumptions.append(&mut between_rule_assumptions);

    let mut rules = rule_path.rules;
    let first = rules.remove(0);

    for other_rule in rules {
        let lhs = vir_expr_to_rsmt2_str(other_rule.lhs.clone());
        let rhs = vir_expr_to_rsmt2_str(other_rule.rhs.clone());
        assumptions.push(format!("(= {} {})", lhs, rhs));
    }

    let assumption_str = format!("(and {})", assumptions.join(" "));
    if !check_assumptions_feasibility(&mut solver, assumption_str.clone()) {
        println!("Rule not applicable as written for PATH assumptions, skipping full query");
        return VerificationResult::InapplicableRule;
    }

    // Correctness query
    // Verification condition: first rule's LHS and RHS are equal
    let first_lhs = vir_expr_to_rsmt2_str(first.lhs);
    let first_rhs = vir_expr_to_rsmt2_str(first.rhs);

    let query = format!(
        "(not (=> {} (= {} {})))",
        assumption_str, first_lhs, first_rhs
    );
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
