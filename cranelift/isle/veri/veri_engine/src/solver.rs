use itertools::Itertools;
/// Convert our internal Verification IR to an external SMT AST and pass
/// queries to that solver.
///
/// Right now, this uses the rsmt2 crate.
use rsmt2::Solver;
use std::collections::{HashMap, HashSet};
use veri_ir::{
    BinaryOp, Counterexample, Expr, RulePath, RuleSemantics, Terminal, Type, TypeContext, UnaryOp,
    VerificationResult,
};

use crate::REG_WIDTH;

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
    fn new_fresh_bits(&mut self, width: usize) -> String {
        let name = format!("fresh{}", self.fresh_bits_idx);
        self.fresh_bits_idx += 1;
        self.additional_decls
            .push((name.clone(), format!("(_ BitVec {})", width)));
        name
    }

    // SMTLIB only supports extends (zero or sign) by concrete amounts, but we
    // need symbolic ones. This method essentially does if-conversion over possible
    // concrete forms, outputting nested ITE blocks. We consider both the starting
    // width and the destination width to be potentially symbolic.
    // For safety, we add an assertion that some arm of this ITE must match.
    fn extend_symbolic(
        &mut self,
        dest_width: &String,
        source: &String,
        source_width: &String,
        op: &str,
    ) -> String {
        // Symbolic expression for amount to shift
        let shift = format!("(- {} {})", dest_width, source_width);

        let mut some_match = vec![];
        let mut ite_str = source.clone();

        // Special case: if we are asked to extend by 0, just return the source
        let matching = format!("(and (= 0 {}))", shift);
        some_match.push(matching.clone());
        ite_str = format!("(ite {} {} {})", matching, source, ite_str);

        // Possible amounts to extend by
        for possible_delta in 1..self.bitwidth + 1 {
            // Possible starting widths
            for possible_source in 1..self.bitwidth + 1 {
                // For now, ignore extends beyond the bitwidth. This is safe because
                // we will fail the rule feasibility check if this is violated.
                if possible_source + possible_delta > self.bitwidth {
                    continue;
                }

                // Statement meaning the symbolic case matches this concrete case
                let matching = format!(
                    "(and (= {} {}) (= {} {}))",
                    possible_delta, shift, possible_source, source_width
                );
                some_match.push(matching.clone());

                // Extract the relevant bits of the source (which is modeled with a wider,
                // register-width bitvector).
                let extract = format!(
                    "((_ extract {} 0) {})",
                    possible_source.wrapping_sub(1),
                    source
                );

                // Do the extend itself.
                let extend = format!("((_ {} {}) {})", op, possible_delta, extract);

                // Pad the extended result back to the full register bitwidth. Use the bits
                // that were already in the source register. That is, given:
                //                       reg - source width              source width
                //                                |                           |
                // SOURCE: [               don't care bits           |   care bits    ]
                //
                //                             dest width
                //                                |
                // OUT:    [ same don't care bits |  defined extend  |   care bits     ]
                let unconstrained_bits = self
                    .bitwidth
                    .checked_sub(possible_delta)
                    .unwrap()
                    .checked_sub(possible_source)
                    .unwrap();

                // If we are extending to the full register width, no padding needed
                let after_padding = if unconstrained_bits == 0 {
                    extend
                } else {
                    let padding = format!(
                        "((_ extract {} {}) {})",
                        self.bitwidth.checked_sub(1).unwrap(),
                        self.bitwidth.checked_sub(unconstrained_bits).unwrap(),
                        source
                    );
                    format!("(concat {} {})", padding, extend)
                };
                ite_str = format!("(ite {} {} {})", matching, after_padding, ite_str);
            }
        }
        let some_shift_matches = format!("(or {})", some_match.join(" "));
        self.width_assumptions.push(some_shift_matches);
        ite_str
    }

    // SMTLIB only supports rotates by concrete amounts, but we
    // need symbolic ones. This method essentially does if-conversion over possible
    // concrete forms, outputting nested ITE blocks. We consider both the starting
    // width and the rotate amount to be potentially symbolic.
    // For safety, we add an assertion that some arm of this ITE must match.
    fn rotate_symbolic(
        &mut self,
        source: &String,
        source_width: &String,
        amount: &String,
        op: &str,
    ) -> String {
        let mut some_match = vec![];
        let mut ite_str = source.clone();

        // Special case: if we are asked to rotate by 0, just return the source
        let matching = format!("(and (= (_ bv0 {}) {}))", self.bitwidth, amount);
        some_match.push(matching.clone());
        ite_str = format!("(ite {} {} {})", matching, source, ite_str);

        // Possible starting widths
        for possible_source in 1..self.bitwidth + 1 {
            // For now, ignore rotates beyond the source width. This is safe because
            // we will fail the rule feasibility check if this is violated.
            // Possible amounts to rotate by
            for possible_rotate in 1..possible_source {
                // Statement meaning the symbolic case matches this concrete case
                let matching = format!(
                    "(and (= (_ bv{} {}) {}) (= {} {}))",
                    possible_rotate, self.bitwidth, amount, possible_source, source_width
                );
                some_match.push(matching.clone());

                // Extract the relevant bits of the source (which is modeled with a wider,
                // register-width bitvector).
                let extract = format!(
                    "((_ extract {} 0) {})",
                    possible_source.wrapping_sub(1),
                    source
                );

                // Do the rotate itself.
                let rotate = format!("((_ {} {}) {})", op, possible_rotate, extract);

                // Pad the extended result back to the full register bitwidth. Use the bits
                // that were already in the source register. That is, given:
                //                       reg - source width              source width
                //                                |                           |
                // SOURCE: [               don't care bits           |   care bits    ]
                //
                //                             dest width
                //                                |
                // OUT:    [ same don't care bits                   |   care bits     ]
                let unconstrained_bits = self.bitwidth.checked_sub(possible_source).unwrap();

                // If we are extending to the full register width, no padding needed
                let after_padding = if unconstrained_bits == 0 {
                    rotate
                } else {
                    let padding = format!(
                        "((_ extract {} {}) {})",
                        self.bitwidth.checked_sub(1).unwrap(),
                        self.bitwidth.checked_sub(unconstrained_bits).unwrap(),
                        source
                    );
                    format!("(concat {} {})", padding, rotate)
                };
                ite_str = format!("(ite {} {} {})", matching, after_padding, ite_str);
            }
        }
        let some_shift_matches = format!("(or {})", some_match.join(" "));
        self.width_assumptions.push(some_shift_matches);
        ite_str
    }

    fn cls(x: &String) -> String {
        String::from("")
    }

    // use param x, return ret, and add unique idents to all intermediate vars
    // rename clz's final result
    fn clz(arg: &String, ret: &String) -> String {
        let s: Vec<&str> = arg.split("_").collect();
        let id = s[s.len() - 1];

        format!("(declare-fun {x} () (_ BitVec 64))

         ; total zeros counter
         (declare-fun ret0_{n} () (_ BitVec 8))
         (assert (= ret0_{n} (_ bv0 8)))

         ; round 1
         (declare-fun ret1_{n} () (_ BitVec 8))
         (declare-fun y32_{n} () (_ BitVec 64))
         (declare-fun x32_{n} () (_ BitVec 64))

         (assert (= y32_{n} (bvlshr {x} #x0000000000000020)))
         (assert (ite (not (= y32_{n} (_ bv0 64))) (= ret1_{n} ret0_{n}) (= ret1_{n} (bvadd ret0_{n} (_ bv32 8)))))
         (assert (ite (not (= y32_{n} (_ bv0 64))) (= x32_{n} y32_{n}) (= x32_{n} {x})))

         ; round 2
         (declare-fun ret2_{n} () (_ BitVec 8))
         (declare-fun y16_{n} () (_ BitVec 64))
         (declare-fun x16_{n} () (_ BitVec 64))

         (assert (= y16_{n} (bvlshr x32_{n} #x0000000000000010)))
         (assert (ite (not (= y16_{n} (_ bv0 64))) (= ret2_{n} ret1_{n}) (= ret2_{n} (bvadd ret1_{n} (_ bv16 8)))))
         (assert (ite (not (= y16_{n} (_ bv0 64))) (= x16_{n} y16_{n}) (= x16_{n} x32_{n})))

         ; round 3
         (declare-fun ret3_{n} () (_ BitVec 8))
         (declare-fun y8_{n} () (_ BitVec 64))
         (declare-fun x8_{n} () (_ BitVec 64))

         (assert (= y8_{n} (bvlshr x16_{n} #x0000000000000008)))
         (assert (ite (not (= y8_{n} (_ bv0 64))) (= ret3_{n} ret2_{n}) (= ret3_{n} (bvadd ret2_{n} (_ bv8 8)))))
         (assert (ite (not (= y8_{n} (_ bv0 64))) (= x8_{n} y8_{n}) (= x8_{n} x16_{n})))

         ; round 4
         (declare-fun ret4_{n} () (_ BitVec 8))
         (declare-fun y4_{n} () (_ BitVec 64))
         (declare-fun x4_{n} () (_ BitVec 64))

         (assert (= y4_{n} (bvlshr x8_{n} #x0000000000000004)))
         (assert (ite (not (= y4_{n} (_ bv0 64))) (= ret4_{n} ret3_{n}) (= ret4_{n} (bvadd ret3_{n} (_ bv4 8)))))
         (assert (ite (not (= y4_{n} (_ bv0 64))) (= x4_{n} y4_{n}) (= x4_{n} x8_{n})))

         ; round 5
         (declare-fun ret5_{n} () (_ BitVec 8))
         (declare-fun y2_{n} () (_ BitVec 64))
         (declare-fun x2_{n} () (_ BitVec 64))

         (assert (= y2_{n} (bvlshr x4_{n} #x0000000000000002)))
         (assert (ite (not (= y2_{n} (_ bv0 64))) (= ret5_{n} ret4_{n}) (= ret5_{n} (bvadd ret4_{n} (_ bv2 8)))))
         (assert (ite (not (= y2_{n} (_ bv0 64))) (= x2_{n} y2_{n}) (= x2_{n} x4_{n})))

         ; round 6
         (declare-fun ret6_{n} () (_ BitVec 8))
         (declare-fun y1_{n} () (_ BitVec 64))
         (declare-fun x1_{n} () (_ BitVec 64))

         (assert (= y1_{n} (bvlshr x2_{n} #x0000000000000001)))
         (assert (ite (not (= y1_{n} (_ bv0 64))) (= ret6_{n} ret5_{n}) (= ret6_{n} (bvadd ret5_{n} (_ bv1 8)))))
         (assert (ite (not (= y1_{n} (_ bv0 64))) (= x1_{n} y1_{n}) (= x1_{n} x2_{n})))

         ; final return
         (declare-fun {r} () (_ BitVec 8))
         (assert (= {r} ret6_{n}))", x = arg, n = id, r = ret)
    }

    pub fn widen_to_query_width(
        &mut self,
        tyvar: u32,
        narrow_width: usize,
        narrow_decl: String,
        name: Option<String>,
    ) -> String {
        let width = self.bitwidth.checked_sub(narrow_width).unwrap();
        if width > 0 {
            let mut narrow_name = format!("narrow__{}", tyvar);
            let mut wide_name = format!("wide__{}", tyvar);
            if let Some(s) = name {
                narrow_name = format!("{}_{}", s, narrow_name);
                wide_name = format!("{}_{}", s, wide_name);
            }
            self.additional_assumptions
                .push(format!("(= {} {})", narrow_name, narrow_decl));
            self.additional_decls
                .push((narrow_name.clone(), format!("(_ BitVec {})", narrow_width)));
            self.additional_decls
                .push((wide_name.clone(), format!("(_ BitVec {})", self.bitwidth)));
            let padding = self.new_fresh_bits(width);
            self.additional_assumptions.push(format!(
                "(= {} (concat {} {}))",
                wide_name, padding, narrow_name,
            ));
            wide_name
        } else {
            if let Some(s) = name {
                // self.additional_decls
                //     .push((s.clone(), format!("(_ BitVec {})", self.bitwidth)));
                self.additional_assumptions
                    .push(format!("(= {} {})", s, narrow_decl));
                s
            } else {
                narrow_decl
            }
        }
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
            Type::BitVector(w) => format!("(_ BitVec {})", w.unwrap_or(self.bitwidth)),
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
        self.width_assumptions.push(format!("(= {} {})", xw, yw));
    }

    pub fn assume_same_width_from_string(&mut self, x: &String, y: &Expr) {
        let yw = self.get_expr_width_var(&y).unwrap().clone();
        self.width_assumptions.push(format!("(= {} {})", x, yw));
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
                Terminal::Var(v) => match self.var_map.get(&v) {
                    Some(o) => o.clone(),
                    None => v,
                },
                Terminal::Const(i) => match ty.unwrap() {
                    Type::BitVector(w) => {
                        let var = *tyvar.unwrap();
                        let width = w.unwrap_or(self.bitwidth);
                        let narrow_decl = format!("(_ bv{} {})", i, width);
                        self.widen_to_query_width(var, width, narrow_decl, None)
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
                match op {
                    BinaryOp::BVAdd | BinaryOp::BVSub | BinaryOp::BVAnd => {
                        self.assume_comparable_types(&*x, &*y)
                    }
                    _ => (),
                };
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
                        let arg_width = self.get_expr_width_var(&*x).unwrap().clone();
                        let xs = self.vir_expr_to_rsmt2_str(*x);
                        let ys = self.vir_expr_to_rsmt2_str(*y);
                        return self.rotate_symbolic(&xs, &arg_width, &ys, "rotate_left");
                        // // SMT bitvector rotate_left requires that the rotate amount be
                        // // statically specified. Instead, to use a dynamic amount, desugar
                        // // to shifts and bit arithmetic.
                        // return format!(
                        //     "(bvor (bvshl {x} {y}) (bvlshr {x} (bvsub {width} {y})))",
                        //     x = self.vir_expr_to_rsmt2_str(*x),
                        //     y = self.vir_expr_to_rsmt2_str(*y),
                        //     width = format!("(_ bv{} {})", self.bitwidth, self.bitwidth)
                        // );
                    }
                    BinaryOp::BVRotr => {
                        let arg_width = self.get_expr_width_var(&*x).unwrap().clone();
                        let xs = self.vir_expr_to_rsmt2_str(*x);
                        let ys = self.vir_expr_to_rsmt2_str(*y);
                        return self.rotate_symbolic(&xs, &arg_width, &ys, "rotate_right");
                    }
                    // To shift right, we need to make sure the bits to the right get zeroed. Shift left first.
                    BinaryOp::BVShr => {
                        let arg_width = self.get_expr_width_var(&*x).unwrap().clone();
                        let xs = self.vir_expr_to_rsmt2_str(*x);
                        let ys = self.vir_expr_to_rsmt2_str(*y);

                        // Strategy: shift right by (bitwidth - arg width) to zero bits to the right
                        // of the bits in the argument size. Then shift right by (amt + (bitwidth - arg width))

                        // Width math
                        let arg_width_as_bv =
                            format!("((_ int2bv {}) {})", self.bitwidth, arg_width);
                        let bitwidth_as_bv = format!("(_ bv{} {})", self.bitwidth, self.bitwidth);
                        let extra_shift =
                            format!(" (bvsub {} {})", bitwidth_as_bv, arg_width_as_bv);
                        let shl_to_zero = format!("(bvshl {} {})", xs, extra_shift);

                        let amt_plus_extra = format!("(bvadd {} {})", ys, extra_shift);
                        return format!("(bvlshr {} {})", shl_to_zero, amt_plus_extra);
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
                    _ => unreachable!("{:?}", op),
                };
                if op == "=" {
                    // Currently we can only perform clz on vars that represent bvs
                    // And we can only use annotations that directly compare the 
                    // result of clz to some var
                    match (*x.clone(), *y.clone()) {
                        (Expr::CLZ(arg), ret) | (ret, Expr::CLZ(arg)) => {
                            match (*arg.clone(), ret.clone()) {
                                (Expr::Terminal(ref t1), Expr::Terminal(ref t2)) => {
                                    match (t1, t2) {
                                        (Terminal::Var(a), Terminal::Var(r)) => {
                                            SolverCtx::clz(&a, &r)
                                        }
                                        _ => unreachable!("({:?}, {:?})", t1, t2),
                                    }                                  
                                }
                                _ => unreachable!("({:?}, {:?})", arg, ret),
                            }
                        }
                        _ => {
                            format!(
                                "({} {} {})",
                                op,
                                self.vir_expr_to_rsmt2_str(*x),
                                self.vir_expr_to_rsmt2_str(*y)
                            )
                        }
                    }
                } else {
                    format!(
                        "({} {} {})",
                        op,
                        self.vir_expr_to_rsmt2_str(*x),
                        self.vir_expr_to_rsmt2_str(*y)
                    )
                }
            }
            Expr::CLZ(arg) => {
                String::from("")
                // match *arg {
                //     Expr::Terminal(ref t) => {
                //         match t {
                //             Terminal::Var(x) => {
                //                 SolverCtx::clz(&x, &String::from("ret"))
                //             }
                //             _ => unreachable!("{:?}", t),
                //         }
                //     }
                //     _ => unreachable!("{:?}", arg),
                // }
            }
            Expr::CLS(_) => {
                String::from("")
            }
            Expr::BVIntToBV(w, x) => {
                let padded_width = self.bitwidth - w;
                format!(
                    "((_ zero_extend {}) ((_ int2bv {}) {}))",
                    padded_width,
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
            Expr::BVSignExtTo(i, x) => {
                let arg_width = self.get_expr_width_var(&*x).unwrap().clone();
                let expr_width = width.unwrap().clone();
                self.width_assumptions
                    .push(format!("(= {} {})", expr_width, i));
                let xs = self.vir_expr_to_rsmt2_str(*x);
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
                self.extend_symbolic(&is, &xs, &arg_width, &"sign_extend")
            }
            Expr::BVExtract(i, j, x) => {
                assert!(i > j);
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
        println!("Checking assumption feasibility");
        solver.push(1).unwrap();
        for a in assumptions {
            println!("{}", &a);
            solver.assert(a).unwrap();

            // Uncomment to debug specific asserts
            solver.push(2).unwrap();
            let _ = match solver.check_sat() {
                Ok(true) => {
                    println!("Assertion list is feasible");
                    true
                }
                Ok(false) => {
                    println!("Assertion list is infeasible!");
                    panic!();
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

/// Overall query for single rule:
/// <declare vars>
/// (not (=> <assumptions> (= <LHS> <RHS>))))))
/// Overall query for multiple rules (out of date):
/// <declare vars>
/// (not (=> (and
///             <all rules' assumptions>
///             <between rule assumptions>
///             <all but first rule's <LHS> = <RHS>>)
///          (= <first rule LHS> <first rule RHS>))))))
pub fn run_solver(rule_sem: RuleSemantics, query_width: usize) -> VerificationResult {
    println!("Verifying with query width: {}", query_width);
    let mut solver = Solver::default_z3(()).unwrap();

    let mut assumptions: Vec<String> = vec![];

    let mut ctx = SolverCtx {
        tyctx: rule_sem.tyctx,
        bitwidth: REG_WIDTH,
        var_map: HashMap::new(),
        width_vars: HashMap::new(),
        width_assumptions: vec![],
        additional_decls: vec![],
        additional_assumptions: vec![],
        fresh_bits_idx: 0,
    };

    // Use the query width for any free variables with unspecified bitwidths
    let mut query_width_used = false;
    let mut query_bv_set_idxs = HashSet::new();
    for v in &rule_sem.free_vars {
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

    for (_e, t) in &ctx.tyctx.tyvars {
        dbg!(t);
        dbg!(&_e);
        let ty = &ctx.tyctx.tymap[&t];
        match ty {
            Type::BitVector(w) => {
                let width_name = format!("width__{}", t);
                ctx.additional_decls
                    .push((width_name.clone(), "Int".to_string()));
                match w {
                    Some(bitwidth) => {
                        ctx.width_assumptions
                            .push(format!("(= {} {})", width_name, bitwidth));
                    }
                    None => {
                        let bv_set_idx = ctx.tyctx.bv_unknown_width_sets[&t];
                        if query_bv_set_idxs.contains(&bv_set_idx) {
                            ctx.tyctx
                                .tymap
                                .insert(*t, Type::BitVector(Some(query_width)));
                            ctx.width_assumptions
                                .push(format!("(= {} {})", width_name, query_width));
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
            let wide = ctx.widen_to_query_width(
                v.tyvar,
                w.unwrap_or(ctx.bitwidth),
                name.clone(),
                Some(name.to_string()),
            );
            ctx.var_map.insert(name.clone(), wide);
        }
        solver.declare_const(name, var_ty).unwrap();
    }

    println!("Adding explicit assumptions");
    for a in &rule_sem.assumptions {
        let p = ctx.vir_expr_to_rsmt2_str(a.clone());
        println!("\t{}", p);
        assumptions.push(p)
    }
    println!("Adding width assumptions");
    for a in &ctx.width_assumptions {
        println!("\t{}", a);
        assumptions.push(a.clone());
    }
    println!("Adding additional assumptions");
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

    // Correctness query
    // Verification condition: first rule's LHS and RHS are equal
    let width = match (
        ctx.static_width(&rule_sem.lhs),
        ctx.static_width(&rule_sem.rhs),
    ) {
        (Some(w), None) | (None, Some(w)) => w,
        (Some(w1), Some(w2)) => {
            assert_eq!(w1, w2);
            w1
        }
        (None, None) => {
            println!(
                "Width of relevant bits of LHS and RHS unknown, using full register bitwidth: {}",
                REG_WIDTH
            );
            REG_WIDTH
        }
    };

    let lhs = ctx.vir_expr_to_rsmt2_str(rule_sem.lhs);
    let rhs = ctx.vir_expr_to_rsmt2_str(rule_sem.rhs);

    let lhs_care_bits = format!("((_ extract {} {}) {})", width - 1, 0, &lhs);
    let rhs_care_bits = format!("((_ extract {} {}) {})", width - 1, 0, &rhs);

    let side_equality = format!("(= {} {})", lhs_care_bits, rhs_care_bits);
    println!("LHS and RHS equality condition:\n\t{}\n", side_equality);

    let query = format!("(not (=> {} {}))", assumption_str, side_equality);
    println!("Running query");
    // println!("Running query:\n\t{}\n", query);
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
