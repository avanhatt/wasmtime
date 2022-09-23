/// Convert our internal Verification IR to an external SMT AST and pass
/// queries to that solver.
///
/// Right now, this uses the rsmt2 crate.
use rsmt2::{print, Solver};
use std::{collections::HashMap, hash::Hash};
use veri_ir::{
    BinaryOp, Counterexample, Expr, RulePath, Terminal, Type, TypeContext, UnaryOp,
    VerificationResult,
};

const BITWIDTH: usize = 64;

struct SolverCtx {
    tyctx: TypeContext,
    bitwidth: usize,
    query_width: usize,
    width_vars: HashMap<u32, String>,
    width_assumptions: Vec<String>,
    additional_decls: Vec<(String, String)>,
    additional_assumptions: Vec<String>,
}

impl SolverCtx {
    pub fn get_expr_width_var(&self, e: &Expr) -> Option<&String> {
        if let Some(tyvar) = self.tyctx.tyvars.get(e) {
            self.width_vars.get(tyvar)
        } else {
            None
        }
    }

    pub fn vir_to_rsmt2_constant_ty(&self, ty: &Type) -> String {
        match ty {
            Type::BitVector(_) => format!("(_ BitVec {})", self.bitwidth),
            Type::Int => "Int".to_string(),
            Type::Bool => "Bool".to_string(),
        }
    }

    pub fn get_type(&self, x: &Expr) -> Option<&Type> {
        self.tyctx.tymap.get(self.tyctx.tyvars.get(x)?)
    }

    pub fn static_width(&self, x: &Expr) -> usize {
        match self.get_type(x).unwrap() {
            Type::BitVector(Some(w)) => *w,
            _=> unreachable!("static width error")
        }
    }

    pub fn check_comparable_types(&self, x: &Expr, y: &Expr) {
        match (self.get_type(x), self.get_type(y)) {
            (None, _) | (_, None) => panic!("Missing type(s) {:?} {:?}", x, y),
            (Some(Type::Bool), Some(Type::Bool)) | (Some(Type::Int), Some(Type::Int)) => (),
            (Some(Type::BitVector(Some(xw))), Some(Type::BitVector(Some(yw)))) => {
                assert_eq!(xw, yw, "incompatible {:?} {:?}", x, y)
            }
            (xt, yt) => panic!(
                "Incompatible type(s) {:?} ({:?})\n{:?} ({:?})",
                x, xt, y, yt
            ),
        }
    }

    pub fn vir_expr_to_rsmt2_str(&mut self, e: Expr) -> String {
        let tyvar = self.tyctx.tyvars.get(&e);
        let ty = &self.get_type(&e);
        let width = self.get_expr_width_var(&e);
        match e {
            Expr::Terminal(t) => match t {
                Terminal::Var(v) => v,
                Terminal::Const(i) => match ty.unwrap() {
                    Type::BitVector(w) => {
                        let var = tyvar.unwrap();
                        let width = w.unwrap_or(self.query_width);
                        let narrow_name = format!("narrow__{}", var);
                        let wide_name = format!("wide__{}", var);
                        let narrow_decl = format!("(_ bv{} {})", i, width);
                        self.additional_assumptions.push(format!("(= {} {})", narrow_name, narrow_decl));
                        self.additional_decls.push((narrow_name.clone(), format!("(_ BitVec {})", width)));
                        self.additional_decls.push((wide_name.clone(), format!("(_ BitVec {})", self.bitwidth)));

                        let constraint = format!("(= ((_ extract {} {}) {}) {})", width - 1, 0, wide_name, narrow_name);
                        dbg!(&constraint);
                        self.additional_assumptions.push(constraint);

                        wide_name
                    }
                    Type::Int => i.to_string(),
                    Type::Bool => {
                        if i == 0 {
                            "false".to_string()
                        } else {
                            "true".to_string()
                        }
                    }
                },
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
                self.check_comparable_types(&*x, &*y);
                match op {
                    BinaryOp::BVRotl => {
                        // SMT bitvector rotate_left requires that the rotate amount be
                        // statically specified. Instead, to use a dynamic amount, desugar
                        // to shifts and bit arithmetic.
                        return format!(
                            "(bvor (bvshl {x} {y}) (bvlshr {x} (bvsub {width} {y})))",
                            x = self.vir_expr_to_rsmt2_str(*x),
                            y = self.vir_expr_to_rsmt2_str(*y),
                            width = format!("(_ bv{} {})", self.bitwidth, self.bitwidth)
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
                format!(
                    "((_ int2bv {}) {})",
                    BITWIDTH,
                    self.vir_expr_to_rsmt2_str(*x)
                )
            }
            Expr::BVConvTo(y) => self.vir_expr_to_rsmt2_str(*y),
            Expr::BVZeroExt(i, x) => {
                let arg_width = self.get_expr_width_var(&*x).unwrap().clone();
                let expr_width = width.unwrap().clone();
                self.width_assumptions
                    .push(format!("(= {} (+ {} {}))", expr_width, arg_width, i));
                self.vir_expr_to_rsmt2_str(*x)
            }
            Expr::BVConvToVarWidth(x, y) => {
                let expr_width = width.unwrap().clone();
                let dyn_width = self.vir_expr_to_rsmt2_str(*x);
                self.width_assumptions
                    .push(format!("(= {} {})", expr_width, dyn_width));
                self.vir_expr_to_rsmt2_str(*y)
            }
            // TODO fix sign
            Expr::BVSignedConvToVarWidth(x, y) => {
                let expr_width = width.unwrap().clone();
                let dyn_width = self.vir_expr_to_rsmt2_str(*x);
                self.width_assumptions
                    .push(format!("(= {} {})", expr_width, dyn_width));
                self.vir_expr_to_rsmt2_str(*y)
            }
            Expr::UndefinedTerm(term) => term.ret.name,
            Expr::WidthOf(x) => self.get_expr_width_var(&*x).unwrap().clone(),

            // AVH TODO: handle widths here
            Expr::BVSignedConvTo(y) => self.vir_expr_to_rsmt2_str(*y),

            Expr::BVSignExt(_i, x) => self.vir_expr_to_rsmt2_str(*x),
            Expr::BVExtract(i, j, x) => self.vir_expr_to_rsmt2_str(*x),
            Expr::Conditional(c, t, e) => {
                format!(
                    "(ite {} {} {})",
                    self.vir_expr_to_rsmt2_str(*c),
                    self.vir_expr_to_rsmt2_str(*t),
                    self.vir_expr_to_rsmt2_str(*e)
                )
            }
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
}

/// Overall query:
/// <declare vars>
/// (not (=> (and
///             <all rules' assumptions>
///             <between rule assumptions>
///             <all but first rule's <LHS> = <RHS>>)
///          (= <first rule LHS> <first rule RHS>))))))
pub fn run_solver_rule_path(
    rule_path: RulePath,
    tyctx: TypeContext,
    query_width: usize,
) -> VerificationResult {
    println!("Verifying with query width: {}", query_width);
    let mut solver = Solver::default_z3(()).unwrap();

    let mut assumptions: Vec<String> = vec![];
    let mut between_rule_assumptions: Vec<String> = vec![];

    let mut ctx = SolverCtx {
        tyctx,
        bitwidth: BITWIDTH,
        query_width,
        width_vars: HashMap::new(),
        width_assumptions: vec![],
        additional_decls: vec![],
        additional_assumptions: vec![],
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
    // Use the query width for any unspecified bitwidths
    let mut query_width_used = false;
    for (e, t) in &ctx.tyctx.tyvars {
        let ty = &ctx.tyctx.tymap[&t];
        match ty {
            Type::BitVector(w) => {
                let width_name = format!("width__{}", t);
                ctx.additional_decls
                    .push((width_name.clone(), "Int".to_string()));
                let width = match w {
                    Some(bitwidth) => *bitwidth,
                    None => {
                        query_width_used = true;
                        ctx.tyctx
                            .tymap
                            .insert(*t, Type::BitVector(Some(query_width)));
                        query_width
                    }
                };
                ctx.width_vars.insert(*t, width_name.clone());
                assumptions.push(format!("(= {} {})", width_name, width));
            }
            _ => (),
        }
    }
    if !query_width_used {
        panic!("Query width unused, check rule!");
    }

    assert_eq!(rule_path.rules.len(), 1);
    let rule_sem = rule_path.rules[0].to_owned();
    println!("Declaring quantified variables");
    for v in &rule_sem.quantified_vars {
        let name = &v.name;
        let var_ty = ctx.vir_to_rsmt2_constant_ty(&v.ty);
        println!("\t{} : {:?}", name, var_ty);
        solver.declare_const(name, var_ty).unwrap();
    }

    println!("Adding explicit assumptions:");
    for a in &rule_sem.assumptions {
        let p = ctx.vir_expr_to_rsmt2_str(a.clone());
        println!("\t{}", p);
        assumptions.push(p)
    }
    println!("Adding width assumptions:");
    for a in &ctx.width_assumptions {
        println!("\t{}", a);
        assumptions.push(a.clone());
    }
    println!("Adding additional assumptions:");
    for a in &ctx.additional_assumptions {
        println!("\t{}", a);
        assumptions.push(a.clone());
    }

    println!("Declaring additional variables");
    for (name, ty) in &ctx.additional_decls {
        println!("\t{} : {:?}", name, ty);
        solver.declare_const(name, ty).unwrap();
    }

    let assumption_str = format!("(and {})", assumptions.join(" "));

    // Check whether the assumptions are possible
    if !ctx.check_assumptions_feasibility(&mut solver, assumption_str.clone()) {
        println!("Rule not applicable as written for rule assumptions, skipping full query");
        return VerificationResult::InapplicableRule;
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
    let lhs_width = ctx.static_width(&first.lhs);
    let rhs_width = ctx.static_width(&first.rhs);
    assert_eq!(lhs_width, rhs_width);

    let first_lhs = ctx.vir_expr_to_rsmt2_str(first.lhs);
    let first_rhs = ctx.vir_expr_to_rsmt2_str(first.rhs);

    let lhs_care_bits =  format!("((_ extract {} {}) {})", lhs_width - 1, 0, &first_lhs);
    let rhs_care_bits = format!("((_ extract {} {}) {})", rhs_width - 1, 0, &first_rhs);
    
    let side_equality = format!("(= {} {})", lhs_care_bits, rhs_care_bits); 
    println!("LHS and RHS equality condition:\n\t{}\n", side_equality);

    let query = format!(
        "(not (=> {} {}))",
        assumption_str, side_equality
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
