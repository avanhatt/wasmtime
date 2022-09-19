/// Convert our internal Verification IR to an external SMT AST and pass
/// queries to that solver.
///
/// Right now, this uses the rsmt2 crate.
use rsmt2::Solver;
use std::collections::HashMap;
use veri_ir::{
    BinaryOp, Counterexample, Expr, RulePath, Terminal, Type, UnaryOp, VerificationResult,
};

const BITWIDTH: usize = 64;

struct Query {
    bv_names: Vec<String>,
    bvwidth_names: Vec<String>,
    bv_decl_idx: usize,
}

struct SolverCtx {
    tymap: HashMap<Expr, Type>,
    bitwidth: usize,
}

impl SolverCtx {
    pub fn vir_to_rsmt2_constant_ty(&self, ty: &Type) -> String {
        match ty {
            Type::BitVector => format!("(_ BitVec {})", BITWIDTH),
            Type::Int => "Int".to_string(),
            Type::Bool => unreachable!(),
        }
    }

    pub fn vir_expr_to_rsmt2_str(&self, e: Expr) -> String {
        let ty = &self.tymap.get(&e);
        match e {
            Expr::Terminal(t) => match t {
                Terminal::Var(v) => v,
                Terminal::Const(i) => {
                    match ty.unwrap() {
                        Type::BitVector => format!("(_ bv{} {})", i, BITWIDTH),
                        Type::Int => i.to_string(),
                        Type::Bool => unreachable!(),
                    }
                }
                Terminal::True => "true".to_string(),
                Terminal::False => "false".to_string(),
            },
            Expr::Unary(op, arg) => {
                let op = match op {
                    UnaryOp::Not => "not",
                    UnaryOp::BVNeg => "bvneg",
                    UnaryOp::BVNot => "bvnot",
                };
                format!("({} {})", op, self.vir_expr_to_rsmt2_str(*arg))
            }
            Expr::Binary(op, x, y) => {
                match op {
                    BinaryOp::BVRotl => {
                        // SMT bitvector rotate_left requires that the rotate amount be
                        // statically specified. Instead, to use a dynamic amount, desugar
                        // to shifts and bit arithmetic.
                        return format!(
                            "(bvor (bvshl {x} {y}) (bvlshr {x} (bvsub {width} {y})))",
                            x = self.vir_expr_to_rsmt2_str(*x),
                            y = self.vir_expr_to_rsmt2_str(*y),
                            width = format!("(_ bv{} {})", BITWIDTH, BITWIDTH)
                        );
                    }
                    _ => (),
                };
                let op = match op {
                    BinaryOp::And => "and",
                    BinaryOp::Or => "or",
                    BinaryOp::Imp => "=>",
                    BinaryOp::Eq => "=",
                    BinaryOp::Lte => "<=",
                    BinaryOp::BVAdd => "bvadd",
                    BinaryOp::BVSub => "bvsub",
                    BinaryOp::BVAnd => "bvand",
                    BinaryOp::BVOr => "bvor",
                    BinaryOp::BVShl => "bvshl",
                    BinaryOp::BVShr => "bvlshr",
                    _ => unreachable!(),
                };
                format!(
                    "({} {} {})",
                    op,
                    self.vir_expr_to_rsmt2_str(*x),
                    self.vir_expr_to_rsmt2_str(*y)
                )
            }
            Expr::BVIntToBV(x) => {
                format!("((_ int2bv {}) {})", BITWIDTH, self.vir_expr_to_rsmt2_str(*x))
            }
            // AVH TODO: handle widths here
            Expr::BVZeroExt(_i, x) => self.vir_expr_to_rsmt2_str(*x),
            Expr::BVSignExt(_i, x) => self.vir_expr_to_rsmt2_str(*x),
            Expr::BVExtract(_i, _j, x) => self.vir_expr_to_rsmt2_str(*x),
            Expr::UndefinedTerm(term) => term.ret.name,
        }
    }

    // Checks whether the assumption list is always false
    fn check_assumptions_feasibility<Parser>(
        &self,
        solver: &mut Solver<Parser>,
        assumptions: String,
    ) -> bool {
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
}

//

/// Overall query:
/// <declare vars>
/// (not (=> <assumptions> (= <LHS> <RHS>))))))
pub fn run_solver_single_rule(rule_sem: veri_ir::RuleSemantics, _ty: &Type) -> VerificationResult {
    todo!()
    // let mut solver = Solver::default_z3(()).unwrap();
    // println!("Declaring constants:");
    // for v in rule_sem.quantified_vars {
    //     todo!()
    //     // let name = v.name.clone();
    //     // let ty = &v.ty;
    //     // match ty.clone() {
    //     //     _ => {
    //     //         let var_ty = vir_to_rsmt2_constant_ty(ty);
    //     //         println!("\t{} : {:?}", name, ty);
    //     //         solver.declare_const(name, var_ty).unwrap();
    //     //     }
    //     // }
    // }

    // // println!("Declaring uninterpreted functions:");
    // // for a in &rule_sem.assumptions {
    // //     declare_uninterp_functions(a.clone(), &mut solver);
    // // }

    // println!("Adding assumptions:");
    // let assumptions: Vec<String> = rule_sem
    //     .assumptions
    //     .iter()
    //     .map(|a| {
    //         let p = vir_expr_to_rsmt2_str(a.clone());
    //         println!("\t{}", p);
    //         p
    //     })
    //     .collect();

    // let assumption_str = format!("(and {})", assumptions.join(" "));

    // // Check whether the assumptions are possible
    // if !check_assumptions_feasibility(&mut solver, assumption_str.clone()) {
    //     println!("Rule not applicable as written, skipping full query");
    //     return VerificationResult::InapplicableRule;
    // }

    // // Correctness query
    // let lhs_s = vir_expr_to_rsmt2_str(rule_sem.lhs);
    // let rhs_s = vir_expr_to_rsmt2_str(rule_sem.rhs);

    // let query = format!("(not (=> {} (= {} {})))", assumption_str, lhs_s, rhs_s);
    // println!("Running query:\n\t{}\n", query);
    // solver.assert(query).unwrap();

    // match solver.check_sat() {
    //     Ok(true) => {
    //         println!("Verification failed");
    //         let model = solver.get_model().unwrap();
    //         dbg!(model);
    //         VerificationResult::Failure(Counterexample {})
    //     }
    //     Ok(false) => {
    //         println!("Verification succeeded");
    //         VerificationResult::Success
    //     }
    //     Err(err) => {
    //         unreachable!("Error! {:?}", err);
    //     }
    // }
}

/// Overall query:
/// <declare vars>
/// (not (=> (and
///             <all rules' assumptions>
///             <between rule assumptions>
///             <all but first rule's <LHS> = <RHS>>)
///          (= <first rule LHS> <first rule RHS>))))))
pub fn run_solver_rule_path(rule_path: RulePath, tymap: HashMap<Expr, Type>) -> VerificationResult {
    let mut solver = Solver::default_z3(()).unwrap();

    let mut assumptions: Vec<String> = vec![];
    let mut between_rule_assumptions: Vec<String> = vec![];

    let ctx = SolverCtx {
        tymap,
        bitwidth: BITWIDTH,
    };

    for (v1, v2) in rule_path.undefined_term_pairs {
        let equality = format!("(= {} {})", v1.ret.name, v2.ret.name);
        between_rule_assumptions.push(equality);
        assert_eq!(v1.args.len(), v2.args.len());
        for (a1, a2) in v1.args.iter().zip(&v2.args) {
            let a1_s = ctx.vir_expr_to_rsmt2_str(a1.clone());
            let a2_s = ctx.vir_expr_to_rsmt2_str(a2.clone());
            let equality = format!("(= {} {})", a1_s, a2_s);
            between_rule_assumptions.push(equality)
        }
    }
    for rule_sem in &rule_path.rules {
        println!("Declaring constants:");
        for v in &rule_sem.quantified_vars {
            let name = &v.name;
            match &v.ty {
                Type::BitVector => {
                    // AVH TODO
                    let var_ty = ctx.vir_to_rsmt2_constant_ty(&veri_ir::Type::BitVector);
                    println!("\t{} : {:?}", name, &var_ty);
                    solver.declare_const(name, var_ty).unwrap();
                }
                _ => {
                    let var_ty = ctx.vir_to_rsmt2_constant_ty(&v.ty);
                    println!("\t{} : {:?}", name, &var_ty);
                    solver.declare_const(name, var_ty).unwrap();
                }
            }
        }

        println!("Adding assumptions:");
        for a in &rule_sem.assumptions {
            let p = ctx.vir_expr_to_rsmt2_str(a.clone());
            println!("\t{}", p);
            assumptions.push(p)
        }

        let assumption_str = format!("(and {})", assumptions.join(" "));

        // Check whether the assumptions are possible
        if !ctx.check_assumptions_feasibility(&mut solver, assumption_str.clone()) {
            println!("Rule not applicable as written for rule assumptions, skipping full query");
            return VerificationResult::InapplicableRule;
        }
    }

    println!("Adding assumptions on relationship between rules");
    assumptions.append(&mut between_rule_assumptions);

    let mut rules = rule_path.rules;
    let first = rules.remove(0);

    for other_rule in rules {
        let lhs = ctx.vir_expr_to_rsmt2_str(other_rule.lhs.clone());
        let rhs = ctx.vir_expr_to_rsmt2_str(other_rule.rhs.clone());
        assumptions.push(format!("(= {} {})", lhs, rhs));
    }

    let assumption_str = format!("(and {})", assumptions.join(" "));
    if !ctx.check_assumptions_feasibility(&mut solver, assumption_str.clone()) {
        println!("Rule not applicable as written for PATH assumptions, skipping full query");
        return VerificationResult::InapplicableRule;
    }

    // Correctness query
    // Verification condition: first rule's LHS and RHS are equal
    let first_lhs = ctx.vir_expr_to_rsmt2_str(first.lhs);
    let first_rhs = ctx.vir_expr_to_rsmt2_str(first.rhs);

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
