use itertools::Itertools;
/// Convert our internal Verification IR to an external SMT AST and pass
/// queries to that solver.
///
/// Right now, this uses the rsmt2 crate.
use rsmt2::Solver;
use std::{
    collections::{HashMap, HashSet},
};
use veri_ir::{
    BinaryOp, Counterexample, Expr, RulePath, Terminal, Type, TypeContext, UnaryOp,
    VerificationResult,
};

const BITWIDTH: usize = 64;

struct SolverCtx {
    tyctx: TypeContext,
    bitwidth: usize,
    var_map: HashMap<String, String>,
    width_vars: HashMap<u32, String>,
    width_assumptions: Vec<String>,
    additional_decls: Vec<(String, String)>,
    additional_assumptions: Vec<String>,
    fresh_bits_idx: usize,
}

impl SolverCtx {

    fn extract_symbolic(
        &mut self,
        source: &String,
        width: &String,
    ) -> String {
        let possible_widths = 1..2;
        // let possible_widths = 0..self.bitwidth;
        let some_width_matches = format!(
            "(or {})",
            possible_widths.clone().map(|s| format!("(= {} {})", s, width)).join(" ") 
        );
        self.additional_assumptions.push(some_width_matches);
        let mut ite_str = source.clone();
        for possible_width in possible_widths {
            let extract = format!("((_ extract {} 0) {})", possible_width - 1, source);
            ite_str = format!("(ite (= {} {}) {} {})", possible_width, width, extract, ite_str);
        }
        ite_str
    }

    fn new_fresh_bits(&mut self, width: usize) -> String {
        let name = format!("fresh{}", self.fresh_bits_idx);
        self.fresh_bits_idx += 1;
        self.additional_decls
            .push((name.clone(), format!("(_ BitVec {})", width)));
        name
    }

    fn extend_symbolic(
        &mut self,
        dest_width: &String,
        source: &String,
        source_width: &String,
        op: &str,
    ) -> String {
        let shift = format!("(- {} {})", dest_width, source_width);
        let possible_shifts = 0..self.bitwidth;
        let some_shift_matches = format!(
            "(or {})",
            possible_shifts.clone().map(|s| format!("(= {} {})", s, shift)).join(" ") 
        );
        self.additional_assumptions.push(some_shift_matches);
        let mut ite_str = source.clone();
        for possible_shift in possible_shifts {
            for possible_source in 1..self.bitwidth {
                if possible_source + possible_shift >= self.bitwidth {continue;}
                let extract = format!("((_ extract {} 0) {})", possible_source.wrapping_sub(1), source);
                let extend = format!("((_ {} {}) {})", op, possible_shift, extract);
                let unconstrained_bits = self.bitwidth.wrapping_sub(possible_shift).wrapping_sub(possible_source);
                let padding = format!("((_ extract {} {}) {})", self.bitwidth.wrapping_sub(1), self.bitwidth.wrapping_sub(unconstrained_bits), source);
                let padded = format!("(concat {} {})", padding, extend);
                ite_str = format!(
                    "(ite (and (= {} {}) (= {} {})) {} {})", 
                    possible_shift, 
                    shift, 
                    possible_source,
                    source_width,
                    padded, 
                    ite_str);
            }
        }
        ite_str
    }

    pub fn widen_to_query_width(
        &mut self,
        tyvar: u32,
        narrow_width: usize,
        narrow_decl: String,
    ) -> String {
        let narrow_name = format!("narrow__{}", tyvar);
        let wide_name = format!("wide__{}", tyvar);
        self.additional_assumptions
            .push(format!("(= {} {})", narrow_name, narrow_decl));
        self.additional_decls
            .push((narrow_name.clone(), format!("(_ BitVec {})", narrow_width)));
        self.additional_decls
            .push((wide_name.clone(), format!("(_ BitVec {})", self.bitwidth)));

        let constraint = format!(
            "(= ((_ extract {} {}) {}) {})",
            narrow_width - 1,
            0,
            wide_name,
            narrow_name
        );
        self.additional_assumptions.push(constraint);
        wide_name
    }

    pub fn get_expr_width_var(&self, e: &Expr) -> Option<&String> {
        if let Some(tyvar) = self.tyctx.tyvars.get(e) {
            self.width_vars.get(tyvar)
        } else {
            None
        }
    }

    pub fn vir_to_rsmt2_constant_ty(&self, ty: &Type) -> String {
        match ty {
            Type::BitVector(w) => format!("(_ BitVec {})", w.unwrap()),
            Type::Int => "Int".to_string(),
            Type::Bool => "Bool".to_string(),
        }
    }

    pub fn get_type(&self, x: &Expr) -> Option<&Type> {
        self.tyctx.tymap.get(self.tyctx.tyvars.get(x)?)
    }

    pub fn static_width(&self, x: &Expr) -> Option<usize> {
        match self.get_type(x).unwrap() {
            Type::BitVector(w) => *w,
            _ => unreachable!("static width error"),
        }
    }

    pub fn assume_same_width(&mut self, x: &Expr, y: &Expr) {
        let xw = self.get_expr_width_var(&x).unwrap().clone();
        let yw = self.get_expr_width_var(&y).unwrap().clone();
        self.additional_assumptions
            .push(format!("(= {} {})", xw, yw));
    }

    pub fn assume_same_width_from_string(&mut self, x: &String, y: &Expr) {
        let yw = self.get_expr_width_var(&y).unwrap().clone();
        self.additional_assumptions
            .push(format!("(= {} {})", x, yw));
    }

    pub fn assume_comparable_types(&mut self, x: &Expr, y: &Expr) {
        match (self.get_type(x), self.get_type(y)) {
            (None, _) | (_, None) => panic!("Missing type(s) {:?} {:?}", x, y),
            (Some(Type::Bool), Some(Type::Bool)) | (Some(Type::Int), Some(Type::Int)) => (),
            (Some(Type::BitVector(Some(xw))), Some(Type::BitVector(Some(yw)))) => {
                assert_eq!(xw, yw, "incompatible {:?} {:?}", x, y)
            }
            (_, _) => self.assume_same_width(x, y),
        }
    }

    pub fn vir_expr_to_rsmt2_str(&mut self, e: Expr) -> String {
        let tyvar = self.tyctx.tyvars.get(&e);
        let ty = &self.get_type(&e);
        let width = self.get_expr_width_var(&e).map(|s| s.clone());
        match e {
            Expr::Terminal(t) => match t {
                Terminal::Var(v) => {
                    match self.var_map.get(&v) {
                        Some(o) => o.clone(),
                        None => v,
                    }
                }
                Terminal::Const(i) => match ty.unwrap() {
                    Type::BitVector(w) => {
                        let var = *tyvar.unwrap();
                        let width = w.unwrap();
                        let narrow_decl = format!("(_ bv{} {})", i, width);
                        self.widen_to_query_width(var, width, narrow_decl)
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
                    UnaryOp::BVNeg => {
                        self.assume_same_width_from_string(&width.unwrap(), &*arg);
                        "bvneg"
                    }
                    UnaryOp::BVNot => {
                        self.assume_same_width_from_string(&width.unwrap(), &*arg);
                        "bvnot"
                    }
                };
                format!("({} {})", op, self.vir_expr_to_rsmt2_str(*arg))
            }
            Expr::Binary(op, x, y) => {
                self.assume_comparable_types(&*x, &*y);
                match op {
                    BinaryOp::BVAdd
                    | BinaryOp::BVSub
                    | BinaryOp::BVAnd
                    | BinaryOp::BVOr
                    | BinaryOp::BVShl
                    | BinaryOp::BVShr
                    | BinaryOp::BVRotl => self.assume_same_width_from_string(&width.unwrap(), &*x),
                    _ => (),
                };
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
            Expr::BVIntToBV(w, x) => {
                format!(
                    "((_ int2bv {}) {})",
                    w,
                    self.vir_expr_to_rsmt2_str(*x)
                )
            }
            Expr::BVConvTo(y) => {
                // For static convto, width constraints are handling during inference
                self.vir_expr_to_rsmt2_str(*y)
            }
            Expr::BVZeroExtTo(i, x) => {
                let arg_width = self.get_expr_width_var(&*x).unwrap().clone();
                let expr_width = width.unwrap().clone();
                self.width_assumptions
                    .push(format!("(= {} {})", expr_width, i));
                let xs = self.vir_expr_to_rsmt2_str(*x);
                let shifts = vec![1, 2, 4, 8, 16, 32, 64];
                let is = i.to_string();
                self.extend_symbolic(&is, &xs, &arg_width, &"zero_extend")
            }
            Expr::BVZeroExtToVarWidth(i, x) => {
                let arg_width = self.get_expr_width_var(&*x).unwrap().clone();
                let expr_width = width.unwrap().clone();
                let is = self.vir_expr_to_rsmt2_str(*i);
                let xs = self.vir_expr_to_rsmt2_str(*x);
                self.width_assumptions
                    .push(format!("(= {} {})", expr_width, is));
                let shifts = vec![1, 2, 4, 8, 16, 32, 64];
                self.extend_symbolic(&is, &xs, &arg_width, &"zero_extend")
            }
            Expr::BVConvToVarWidth(x, y) => {
                let expr_width = width.unwrap().clone();
                let dyn_width = self.vir_expr_to_rsmt2_str(*x);
                self.width_assumptions
                    .push(format!("(= {} {})", expr_width, dyn_width));
                self.vir_expr_to_rsmt2_str(*y)
            }
            Expr::UndefinedTerm(term) => term.ret.name,
            Expr::WidthOf(x) => self.get_expr_width_var(&*x).unwrap().clone(),
            Expr::BVSignExt(i, x) => {
                let arg_width = self.get_expr_width_var(&*x).unwrap().clone();
                let expr_width = width.unwrap().clone();
                self.width_assumptions
                    .push(format!("(= {} {})", expr_width, i));
                let xs = self.vir_expr_to_rsmt2_str(*x);
                let shifts = vec![1, 2, 4, 8, 16, 32, 64];
                let is = i.to_string();
                self.extend_symbolic(&is, &xs, &arg_width, &"sign_extend")
            }
            Expr::BVSignExtToVarWidth(i, x) => {
                let arg_width = self.get_expr_width_var(&*x).unwrap().clone();
                let expr_width = width.unwrap().clone();
                let is = self.vir_expr_to_rsmt2_str(*i);
                let xs = self.vir_expr_to_rsmt2_str(*x);
                self.width_assumptions
                    .push(format!("(= {} {})", expr_width, is));
                let shifts = vec![1, 2, 4, 8, 16, 32, 64];
                self.extend_symbolic(&is, &xs, &arg_width, &"zero_extend")
            }
            Expr::BVExtract(i, j, x) => {
                assert!(i > j);
                assert!(j >= 0);
                assert!(i < self.bitwidth);
                let xs = self.vir_expr_to_rsmt2_str(*x);
                let extract = format!("((_ extract {} {}) {})", i, j, xs);
                let new_width = i - j + 1;
                let padding = self.new_fresh_bits(self.bitwidth.checked_sub(new_width).unwrap());
                format!("(concat {} {})", padding, extract)

            }
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
        assumptions: Vec<String>,
    ) -> bool {
        solver.push(1).unwrap();
        for a in assumptions {
            println!("{}", a);
            solver.assert(a).unwrap();
            solver.push(2).unwrap();

            let _ = match solver.check_sat() {
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

            solver.pop(2).unwrap();
        }
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
        var_map: HashMap::new(),
        width_vars: HashMap::new(),
        width_assumptions: vec![],
        additional_decls: vec![],
        additional_assumptions: vec![],
        fresh_bits_idx: 0,
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

    assert_eq!(rule_path.rules.len(), 1);
    let rule_sem = rule_path.rules[0].to_owned();

    // Use the query width for any quantified variables with unspecified bitwidths
    let mut query_width_used = false;
    let mut query_bv_set_idxs = HashSet::new();
    for v in &rule_sem.quantified_vars {
        let ty = &ctx.tyctx.tymap[&v.tyvar];
        if let Type::BitVector(None) = ty {
            query_width_used = true;
            ctx.tyctx
                .tymap
                .insert(v.tyvar, Type::BitVector(Some(query_width)));
            let bv_set_idx = ctx.tyctx.bv_unknown_width_sets[&v.tyvar];
            query_bv_set_idxs.insert(bv_set_idx);
        }
    }
    if !query_width_used {
        panic!("Query width unused, check rule!");
    }

    for (e, t) in &ctx.tyctx.tyvars {
        let ty = &ctx.tyctx.tymap[&t];
        match ty {
            Type::BitVector(w) => {
                let width_name = format!("width__{}", t);
                ctx.additional_decls
                    .push((width_name.clone(), "Int".to_string()));
                match w {
                    Some(bitwidth) => {
                        assumptions.push(format!("(= {} {})", width_name, bitwidth));
                    }
                    None => {
                        let bv_set_idx = ctx.tyctx.bv_unknown_width_sets[&t];
                        if query_bv_set_idxs.contains(&bv_set_idx) {
                            ctx.tyctx
                                .tymap
                                .insert(*t, Type::BitVector(Some(query_width)));
                        }
                    }
                };
                ctx.width_vars.insert(*t, width_name.clone());
            }
            _ => (),
        }
    }

    println!("Declaring quantified variables");
    for v in &rule_sem.quantified_vars {
        let name = &v.name;
        let ty = ctx.tyctx.tymap[&v.tyvar].clone();
        let var_ty = ctx.vir_to_rsmt2_constant_ty(&ty);
        println!("\t{} : {:?}", name, var_ty);
        if let Type::BitVector(w) = ty {
            let wide = ctx.widen_to_query_width(v.tyvar, w.unwrap(), name.clone());
            ctx.var_map.insert(name.clone(), wide);
        }
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
    if !ctx.check_assumptions_feasibility(&mut solver, assumptions) {
        println!("Rule not applicable as written for rule assumptions, skipping full query");
        return VerificationResult::InapplicableRule;
    }

    // println!("Adding assumptions on relationship between rules");
    // assumptions.append(&mut between_rule_assumptions);

    let mut rules = rule_path.rules;
    let first = rules.remove(0);

    // for other_rule in rules {
    //     let lhs = ctx.vir_expr_to_rsmt2_str(other_rule.lhs.clone());
    //     let rhs = ctx.vir_expr_to_rsmt2_str(other_rule.rhs.clone());
    //     assumptions.push(format!("(= {} {})", lhs, rhs));
    // }

    // let assumption_str = format!("(and {})", assumptions.join(" "));
    // if !ctx.check_assumptions_feasibility(&mut solver, assumption_str.clone()) {
    //     println!("Rule not applicable as written for PATH assumptions, skipping full query");
    //     return VerificationResult::InapplicableRule;
    // }

    // Correctness query
    // Verification condition: first rule's LHS and RHS are equal
    let width = match (ctx.static_width(&first.lhs), ctx.static_width(&first.rhs)) {
        (Some(w), None) | (None, Some(w)) => w,
        (Some(w1), Some(w2)) => {
            assert_eq!(w1, w2);
            w1
        }
        (None, None) => {
            println!(
                "Width of relevant bits of LHS and RHS unknown, using full register bitwidth: {}",
                BITWIDTH
            );
            BITWIDTH
        }
    };

    let first_lhs = ctx.vir_expr_to_rsmt2_str(first.lhs);
    let first_rhs = ctx.vir_expr_to_rsmt2_str(first.rhs);

    let lhs_care_bits = format!("((_ extract {} {}) {})", width - 1, 0, &first_lhs);
    let rhs_care_bits = format!("((_ extract {} {}) {})", width - 1, 0, &first_rhs);

    let side_equality = format!("(= {} {})", lhs_care_bits, rhs_care_bits);
    println!("LHS and RHS equality condition:\n\t{}\n", side_equality);

    let query = format!("(not (=> {} {}))", assumption_str, side_equality);
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
