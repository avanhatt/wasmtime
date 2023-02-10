/// Convert our internal Verification IR to an external SMT AST and pass
/// queries to that solver.
///
/// This uses the easy-smt crate to interact with any solver.
use easy_smt::{Response, SExpr};
use log::debug;
use std::collections::HashMap;
use veri_ir::{
    BinaryOp, Counterexample, Expr, RuleSemantics, Terminal, Type, TypeContext, UnaryOp,
    VerificationResult,
};

mod encoded_ops;

use encoded_ops::cls;
use encoded_ops::clz;
use encoded_ops::rev;

use crate::REG_WIDTH;

pub struct SolverCtx {
    smt: easy_smt::Context,
    tyctx: TypeContext,
    pub bitwidth: usize,
    var_map: HashMap<String, SExpr>,
    width_vars: HashMap<u32, String>,
    width_assumptions: Vec<SExpr>,
    pub additional_decls: Vec<(String, SExpr)>,
    pub additional_assumptions: Vec<SExpr>,
    fresh_bits_idx: usize,
}

impl SolverCtx {
    pub fn new_fresh_bits(&mut self, width: usize) -> SExpr {
        let name = format!("fresh{}", self.fresh_bits_idx);
        self.fresh_bits_idx += 1;
        self.additional_decls
            .push((name.clone(), self.smt.bit_vec_sort(self.smt.numeral(width))));
        self.smt.atom(name)
    }

    fn new_fresh_int(&mut self) -> SExpr {
        let name = format!("fresh{}", self.fresh_bits_idx);
        self.fresh_bits_idx += 1;
        self.additional_decls
            .push((name.clone(), self.smt.int_sort()));
        self.smt.atom(name)
    }

    fn new_fresh_bool(&mut self) -> SExpr {
        let name = format!("fresh{}", self.fresh_bits_idx);
        self.fresh_bits_idx += 1;
        self.additional_decls
            .push((name.clone(), self.smt.bool_sort()));
        self.smt.atom(name)
    }

    fn declare(&mut self, name: String, typ: SExpr) -> SExpr {
        let atom = self.smt.atom(&name);
        self.additional_decls.push((name, typ));
        atom
    }

    fn assume(&mut self, expr: SExpr) {
        self.additional_assumptions.push(expr);
    }

    /// Construct a constant bit-vector value of the given width. (This is used so pervasively that
    /// perhaps we should submit it for inclusion in the easy_smt library...) (Also, this is
    /// generic because we use it with several integer types, but it probably shouldn't be *this*
    /// generic.)
    fn bv<T: std::fmt::Display>(&self, value: T, width: usize) -> SExpr {
        self.smt.list(vec![
            self.smt.atoms().und,
            self.smt.atom(format!("bv{}", value)),
            self.smt.numeral(width),
        ])
    }

    /// Convert an SMT integer to a bit vector of a given width.
    fn int2bv(&self, width: usize, value: SExpr) -> SExpr {
        self.smt.list(vec![
            self.smt.list(vec![
                self.smt.atoms().und,
                self.smt.atom("int2bv"),
                self.smt.numeral(width),
            ]),
            value,
        ])
    }

    /// Convert an SMT bit vector to a nat.
    fn bv2nat(&self, value: SExpr) -> SExpr {
        self.smt.list(vec![self.smt.atom("bv2nat"), value])
    }

    /// Zero-extend an SMT bit vector to a wider bit vector by adding `padding` zeroes to the
    /// front.
    fn zero_extend(&self, padding: usize, value: SExpr) -> SExpr {
        self.smt.list(vec![
            self.smt.list(vec![
                self.smt.atoms().und,
                self.smt.atom("zero_extend"),
                self.smt.numeral(padding),
            ]),
            value,
        ])
    }

    // Extend with concrete source and destination sizes. Includes extracting relevant bits.
    fn extend_concrete(
        &mut self,
        dest_width: usize,
        source: SExpr,
        source_width: usize,
        op: &str,
    ) -> SExpr {
        if dest_width < source_width {
            self.additional_assumptions.push(self.smt.false_());
            return source;
        }

        let delta = dest_width - source_width;
        // Extract the relevant bits of the source (which is modeled with a wider,
        // register-width bitvector).
        let extract = self
            .smt
            .extract(source_width.wrapping_sub(1).try_into().unwrap(), 0, source);

        // Do the extend itself.
        let extend = self.smt.list(vec![
            self.smt.list(vec![
                self.smt.atoms().und,
                self.smt.atom(op),
                self.smt.numeral(delta),
            ]),
            extract,
        ]);

        // Pad the extended result back to the full register bitwidth. Use the bits
        // that were already in the source register. That is, given:
        //                       reg - source width              source width
        //                                |                           |
        // SOURCE: [               don't care bits           |   care bits    ]
        //
        //                             dest width
        //                                |
        // OUT:    [ same don't care bits |  defined extend  |   care bits     ]
        let mut unconstrained_bits = 0;
        if dest_width < self.bitwidth {
            unconstrained_bits = self
                .bitwidth
                .checked_sub(delta)
                .unwrap()
                .checked_sub(source_width)
                .unwrap();
        }

        // If we are extending to the full register width, no padding needed
        if unconstrained_bits == 0 {
            extend
        } else {
            let padding = self.smt.extract(
                self.bitwidth.checked_sub(1).unwrap().try_into().unwrap(),
                self.bitwidth
                    .checked_sub(unconstrained_bits)
                    .unwrap()
                    .try_into()
                    .unwrap(),
                source,
            );
            self.smt.concat(padding, extend)
        }
    }

    // SMTLIB only supports extends (zero or sign) by concrete amounts, but we
    // need symbolic ones. This method essentially does if-conversion over possible
    // concrete forms, outputting nested ITE blocks. We consider both the starting
    // width and the destination width to be potentially symbolic.
    // For safety, we add an assertion that some arm of this ITE must match.
    fn extend_symbolic(
        &mut self,
        dest_width: SExpr,
        source: SExpr,
        source_width: SExpr,
        op: &str,
    ) -> SExpr {
        // Symbolic expression for amount to shift
        let shift = self.smt.sub(dest_width, source_width);

        let mut some_match = vec![];
        let mut ite_str = source.clone();

        // Special case: if we are asked to extend by 0, just return the source
        let matching = self.smt.eq(self.smt.numeral(0), shift);
        some_match.push(matching.clone());
        ite_str = self.smt.ite(matching, source, ite_str);

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
                let matching = self.smt.and(
                    self.smt.eq(self.smt.numeral(possible_delta), shift),
                    self.smt.eq(self.smt.numeral(possible_source), source_width),
                );
                some_match.push(matching.clone());
                let extend = self.extend_concrete(
                    possible_source + possible_delta,
                    source,
                    possible_source,
                    op,
                );
                ite_str = self.smt.ite(matching, extend, ite_str);
            }
        }
        let some_shift_matches = self.smt.or_many(some_match);
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
        source: SExpr,
        source_width: SExpr,
        amount: SExpr,
        op: &str,
    ) -> SExpr {
        let mut some_match = vec![];
        let mut ite_str = source.clone();

        // Special case: if we are asked to rotate by 0, just return the source
        let matching = self.smt.eq(self.bv(0, self.bitwidth), amount);
        some_match.push(matching.clone());
        ite_str = self.smt.ite(matching, source, ite_str);

        // Possible starting widths
        for possible_source in 1..self.bitwidth + 1 {
            // For now, ignore rotates beyond the source width. This is safe because
            // we will fail the rule feasibility check if this is violated.
            // Possible amounts to rotate by
            for possible_rotate in 1..possible_source {
                // Statement meaning the symbolic case matches this concrete case
                let matching = self.smt.and(
                    self.smt.eq(self.bv(possible_rotate, self.bitwidth), amount),
                    self.smt.eq(self.smt.numeral(possible_source), source_width),
                );
                some_match.push(matching);

                // Extract the relevant bits of the source (which is modeled with a wider,
                // register-width bitvector).
                let extract = self.smt.extract(
                    possible_source.checked_sub(1).unwrap().try_into().unwrap(),
                    0,
                    source,
                );

                // Do the rotate itself.
                let rotate = self.smt.list(vec![
                    self.smt.list(vec![
                        self.smt.atoms().und,
                        self.smt.atom(op),
                        self.smt.numeral(possible_rotate),
                    ]),
                    extract,
                ]);

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
                    let padding = self.smt.extract(
                        self.bitwidth.checked_sub(1).unwrap().try_into().unwrap(),
                        self.bitwidth
                            .checked_sub(unconstrained_bits)
                            .unwrap()
                            .try_into()
                            .unwrap(),
                        source,
                    );
                    self.smt.concat(padding, rotate)
                };
                ite_str = self.smt.ite(matching, after_padding, ite_str);
            }
        }
        let some_shift_matches = self.smt.or_many(some_match);
        self.width_assumptions.push(some_shift_matches);
        ite_str
    }

    pub fn widen_to_query_width(
        &mut self,
        tyvar: u32,
        narrow_width: usize,
        narrow_decl: SExpr,
        name: Option<String>,
    ) -> SExpr {
        let width = self.bitwidth.checked_sub(narrow_width).unwrap();
        if width > 0 {
            let mut narrow_name = format!("narrow__{}", tyvar);
            let mut wide_name = format!("wide__{}", tyvar);
            if let Some(s) = name {
                narrow_name = format!("{}_{}", s, narrow_name);
                wide_name = format!("{}_{}", s, wide_name);
            }
            self.additional_assumptions
                .push(self.smt.eq(self.smt.atom(&narrow_name), narrow_decl));
            self.additional_decls.push((
                narrow_name.clone(),
                self.smt.bit_vec_sort(self.smt.numeral(narrow_width)),
            ));
            self.additional_decls.push((
                wide_name.clone(),
                self.smt.bit_vec_sort(self.smt.numeral(self.bitwidth)),
            ));
            let padding = self.new_fresh_bits(width);
            self.additional_assumptions.push(self.smt.eq(
                self.smt.atom(&wide_name),
                self.smt.concat(padding, self.smt.atom(narrow_name)),
            ));
            self.smt.atom(wide_name)
        } else {
            if let Some(s) = name {
                // self.additional_decls
                //     .push((s.clone(), format!("(_ BitVec {})", self.bitwidth)));
                self.additional_assumptions
                    .push(self.smt.eq(self.smt.atom(&s), narrow_decl));
                self.smt.atom(&s)
            } else {
                narrow_decl
            }
        }
    }

    pub fn get_expr_width_var(&self, e: &Expr) -> Option<SExpr> {
        if let Some(tyvar) = self.tyctx.tyvars.get(e) {
            self.width_vars.get(tyvar).map(|s| self.smt.atom(s))
        } else {
            None
        }
    }

    pub fn vir_to_smt_ty(&self, ty: &Type) -> SExpr {
        match ty {
            Type::BitVector(w) => {
                let width = w.unwrap_or(self.bitwidth);
                self.smt.bit_vec_sort(self.smt.numeral(width))
            }
            Type::Int => self.smt.int_sort(),
            Type::Bool => self.smt.bool_sort(),
        }
    }

    pub fn get_type(&self, x: &Expr) -> Option<&Type> {
        self.tyctx.tymap.get(self.tyctx.tyvars.get(x)?)
    }

    pub fn get_expr_value(&self, e: &Expr) -> Option<i128> {
        if let Some(tyvar) = self.tyctx.tyvars.get(e) {
            if let Some(v) = self.tyctx.tyvals.get(tyvar) {
                Some(*v)
            } else {
                None
            }
        } else {
            None
        }
    }

    pub fn static_width(&self, x: &Expr) -> Option<usize> {
        match self.get_type(x) {
            Some(Type::BitVector(w)) => *w,
            _ => None,
        }
    }

    pub fn assume_same_width(&mut self, x: &Expr, y: &Expr) {
        let xw = self.get_expr_width_var(&x).unwrap().clone();
        let yw = self.get_expr_width_var(&y).unwrap().clone();
        self.width_assumptions.push(self.smt.eq(xw, yw));
    }

    pub fn assume_same_width_from_string(&mut self, x: SExpr, y: &Expr) {
        let yw = self.get_expr_width_var(&y).unwrap().clone();
        self.width_assumptions.push(self.smt.eq(x, yw));
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

    pub fn vir_expr_to_sexp(&mut self, e: Expr) -> SExpr {
        let tyvar = self.tyctx.tyvars.get(&e);
        let ty = self.get_type(&e);
        let width = self.get_expr_width_var(&e).map(|s| s.clone());
        let static_expr_width = self.static_width(&e);
        match e {
            Expr::Terminal(t) => match t {
                Terminal::Var(v) => match self.var_map.get(&v) {
                    Some(o) => *o,
                    None => self.smt.atom(v),
                },
                Terminal::Const(i, _) => match ty.unwrap() {
                    Type::BitVector(w) => {
                        let var = *tyvar.unwrap();
                        let width = w.unwrap_or(self.bitwidth);
                        let narrow_decl = self.bv(i, width);
                        self.widen_to_query_width(var, width, narrow_decl, None)
                    }
                    Type::Int => self.smt.numeral(i),
                    Type::Bool => {
                        if i == 0 {
                            self.smt.false_()
                        } else {
                            self.smt.true_()
                        }
                    }
                },
                Terminal::True => self.smt.true_(),
                Terminal::False => self.smt.false_(),
                Terminal::Wildcard(_) => match ty.unwrap() {
                    Type::BitVector(_) => self.new_fresh_bits(self.bitwidth),
                    Type::Int => self.new_fresh_int(),
                    Type::Bool => self.new_fresh_bool(),
                },
            },
            Expr::Unary(op, arg) => {
                let op = match op {
                    UnaryOp::Not => "not",
                    UnaryOp::BVNeg => {
                        self.assume_same_width_from_string(width.unwrap(), &*arg);
                        "bvneg"
                    }
                    UnaryOp::BVNot => {
                        self.assume_same_width_from_string(width.unwrap(), &*arg);
                        "bvnot"
                    }
                };
                let subexp = self.vir_expr_to_sexp(*arg);
                self.smt.list(vec![self.smt.atom(op), subexp])
            }
            Expr::Binary(op, x, y) => {
                match op {
                    BinaryOp::BVMul
                    | BinaryOp::BVUDiv
                    | BinaryOp::BVAdd
                    | BinaryOp::BVSub
                    | BinaryOp::BVAnd
                    | BinaryOp::BVOr
                    | BinaryOp::BVShl
                    | BinaryOp::BVShr
                    | BinaryOp::BVAShr
                    | BinaryOp::BVRotl => self.assume_same_width_from_string(width.unwrap(), &*x),
                    _ => (),
                };
                match op {
                    BinaryOp::BVAdd | BinaryOp::BVSub | BinaryOp::BVAnd => {
                        self.assume_comparable_types(&*x, &*y)
                    }
                    _ => (),
                };
                match op {
                    BinaryOp::BVRotl => {
                        let arg_width = self.get_expr_width_var(&*x).unwrap().clone();
                        let xs = self.vir_expr_to_sexp(*x);
                        let ys = self.vir_expr_to_sexp(*y);
                        return self.rotate_symbolic(xs, arg_width, ys, "rotate_left");
                        // // SMT bitvector rotate_left requires that the rotate amount be
                        // // statically specified. Instead, to use a dynamic amount, desugar
                        // // to shifts and bit arithmetic.
                        // return format!(
                        //     "(bvor (bvshl {x} {y}) (bvlshr {x} (bvsub {width} {y})))",
                        //     x = self.vir_expr_to_sexp(*x),
                        //     y = self.vir_expr_to_sexp(*y),
                        //     width = format!("(_ bv{} {})", self.bitwidth, self.bitwidth)
                        // );
                    }
                    BinaryOp::BVRotr => {
                        let arg_width = self.get_expr_width_var(&*x).unwrap().clone();
                        let xs = self.vir_expr_to_sexp(*x);
                        let ys = self.vir_expr_to_sexp(*y);
                        return self.rotate_symbolic(xs, arg_width, ys, "rotate_right");
                    }
                    // To shift right, we need to make sure the bits to the right get zeroed. Shift left first.
                    BinaryOp::BVShr => {
                        let arg_width = self.get_expr_width_var(&*x).unwrap().clone();
                        let xs = self.vir_expr_to_sexp(*x);
                        let ys = self.vir_expr_to_sexp(*y);

                        // Strategy: shift left by (bitwidth - arg width) to zero bits to the right
                        // of the bits in the argument size. Then shift right by (amt + (bitwidth - arg width))

                        // Width math
                        let arg_width_as_bv = self.int2bv(self.bitwidth, arg_width);
                        let bitwidth_as_bv = self.bv(self.bitwidth, self.bitwidth);
                        let extra_shift = self.smt.bvsub(bitwidth_as_bv, arg_width_as_bv);
                        let shl_to_zero = self.smt.bvshl(xs, extra_shift);

                        let amt_plus_extra = self.smt.bvadd(ys, extra_shift);
                        return self.smt.bvlshr(shl_to_zero, amt_plus_extra);
                    }
                    BinaryOp::BVAShr => {
                        let arg_width = self.get_expr_width_var(&*x).unwrap().clone();
                        let xs = self.vir_expr_to_sexp(*x);
                        let ys = self.vir_expr_to_sexp(*y);

                        // Strategy: shift left by (bitwidth - arg width) to eliminate bits to the left
                        // of the bits in the argument size. Then shift right by (amt + (bitwidth - arg width))

                        // Width math
                        let arg_width_as_bv = self.int2bv(self.bitwidth, arg_width);
                        let bitwidth_as_bv = self.bv(self.bitwidth, self.bitwidth);
                        let extra_shift = self.smt.bvsub(bitwidth_as_bv, arg_width_as_bv);
                        let shl_to_zero = self.smt.bvshl(xs, extra_shift);

                        let amt_plus_extra = self.smt.bvadd(ys, extra_shift);
                        return self.smt.bvashr(shl_to_zero, amt_plus_extra);
                    }
                    _ => (),
                };
                let op_str = match op {
                    BinaryOp::And => "and",
                    BinaryOp::Or => "or",
                    BinaryOp::Imp => "=>",
                    BinaryOp::Eq => "=",
                    // TODO: this comparison only works for Ints!!
                    BinaryOp::Lte => "<=",
                    BinaryOp::BVMul => "bvmul",
                    BinaryOp::BVUDiv => "bvudiv",
                    BinaryOp::BVAdd => "bvadd",
                    BinaryOp::BVSub => "bvsub",
                    BinaryOp::BVAnd => "bvand",
                    BinaryOp::BVOr => "bvor",
                    BinaryOp::BVXor => "bvxor",
                    BinaryOp::BVShl => "bvshl",
                    _ => unreachable!("{:?}", op),
                };
                // If we have some static width that isn't the bitwidth, extract based on it
                // before performing the operation.
                match static_expr_width {
                    Some(w) if w < self.bitwidth => {
                        let h: i32 = (w - 1).try_into().unwrap();
                        let x_sexp = self.vir_expr_to_sexp(*x);
                        let y_sexp = self.vir_expr_to_sexp(*y);
                        self.zero_extend(
                            self.bitwidth.checked_sub(w).unwrap(),
                            self.smt.list(vec![
                                self.smt.atom(op_str),
                                self.smt.extract(h, 0, x_sexp),
                                self.smt.extract(h, 0, y_sexp),
                            ]),
                        )
                    }
                    _ => {
                        let x_sexp = self.vir_expr_to_sexp(*x);
                        let y_sexp = self.vir_expr_to_sexp(*y);
                        self.smt.list(vec![self.smt.atom(op_str), x_sexp, y_sexp])
                    }
                }
            }
            Expr::BVIntToBV(w, x) => {
                let padded_width = self.bitwidth - w;
                let x_sexp = self.vir_expr_to_sexp(*x);
                self.zero_extend(padded_width, self.int2bv(w, x_sexp))
            }
            Expr::BVToInt(x) => {
                let x_sexp = self.vir_expr_to_sexp(*x);
                self.bv2nat(x_sexp)
            }
            Expr::BVConvTo(y) => {
                // For static convto, width constraints are handling during inference
                self.vir_expr_to_sexp(*y)
            }
            Expr::BVZeroExtTo(i, x) => {
                let arg_width = self.get_expr_width_var(&*x).unwrap().clone();
                let static_width = self.static_width(&*x);
                let expr_width = width.unwrap().clone();
                self.width_assumptions
                    .push(self.smt.eq(expr_width, self.smt.numeral(i)));
                let xs = self.vir_expr_to_sexp(*x);
                if let Some(size) = static_width {
                    self.extend_concrete(i, xs, size, &"zero_extend")
                } else {
                    self.extend_symbolic(self.smt.numeral(i), xs, arg_width, &"zero_extend")
                }
            }
            Expr::BVZeroExtToVarWidth(i, x) => {
                let arg_width = self.get_expr_width_var(&*x).unwrap().clone();
                let static_arg_width = self.static_width(&*x);
                let expr_width = width.unwrap().clone();
                let is = self.vir_expr_to_sexp(*i);
                let xs = self.vir_expr_to_sexp(*x);
                self.width_assumptions.push(self.smt.eq(expr_width, is));
                if let (Some(arg_size), Some(e_size)) = (static_arg_width, static_expr_width) {
                    self.extend_concrete(e_size, xs, arg_size, &"zero_extend")
                } else {
                    self.extend_symbolic(is, xs, arg_width, &"zero_extend")
                }
            }
            Expr::BVSignExtTo(i, x) => {
                let arg_width = self.get_expr_width_var(&*x).unwrap().clone();
                let static_width = self.static_width(&*x);
                let expr_width = width.unwrap().clone();
                self.width_assumptions
                    .push(self.smt.eq(expr_width, self.smt.numeral(i)));
                let xs = self.vir_expr_to_sexp(*x);
                if let Some(size) = static_width {
                    self.extend_concrete(i, xs, size, &"sign_extend")
                } else {
                    self.extend_symbolic(self.smt.numeral(i), xs, arg_width, "sign_extend")
                }
            }
            Expr::BVSignExtToVarWidth(i, x) => {
                let arg_width = self.get_expr_width_var(&*x).unwrap().clone();
                let static_arg_width = self.static_width(&*x);
                let expr_width = width.unwrap().clone();
                let is = self.vir_expr_to_sexp(*i);
                let xs = self.vir_expr_to_sexp(*x);
                self.width_assumptions.push(self.smt.eq(expr_width, is));
                if let (Some(arg_size), Some(e_size)) = (static_arg_width, static_expr_width) {
                    self.extend_concrete(e_size, xs, arg_size, &"sign_extend")
                } else {
                    self.extend_symbolic(is, xs, arg_width, &"sign_extend")
                }
            }
            Expr::BVConvToVarWidth(x, y) => {
                let expr_width = width.unwrap().clone();
                let dyn_width = self.vir_expr_to_sexp(*x);
                self.width_assumptions
                    .push(self.smt.eq(expr_width, dyn_width));
                self.vir_expr_to_sexp(*y)
            }
            Expr::UndefinedTerm(term) => self.smt.atom(term.ret.name),
            Expr::WidthOf(x) => self.get_expr_width_var(&*x).unwrap().clone(),
            Expr::BVExtract(i, j, x) => {
                assert!(i >= j);
                if let Type::BitVector(x_width) = self.get_type(&x).unwrap() {
                    assert!(i < self.bitwidth);
                    assert!(i < x_width.unwrap());
                    let xs = self.vir_expr_to_sexp(*x);
                    // No-op if we are extracting exactly the full bitwidth
                    if j == 0 && i == self.bitwidth - 1 {
                        return xs;
                    }
                    let extract =
                        self.smt
                            .extract(i.try_into().unwrap(), j.try_into().unwrap(), xs);
                    let new_width = i - j + 1;
                    if new_width < self.bitwidth {
                        let padding =
                            self.new_fresh_bits(self.bitwidth.checked_sub(new_width).unwrap());
                        self.smt.concat(padding, extract)
                    } else {
                        extract
                    }
                } else {
                    unreachable!("Must perform extraction on bv with known width")
                }
            }
            Expr::Conditional(c, t, e) => {
                let c_sexp = self.vir_expr_to_sexp(*c);
                let t_sexp = self.vir_expr_to_sexp(*t);
                let e_sexp = self.vir_expr_to_sexp(*e);
                self.smt.ite(c_sexp, t_sexp, e_sexp)
            }
            Expr::CLZ(e) => {
                let tyvar = *tyvar.unwrap();
                let es = self.vir_expr_to_sexp(*e);
                match static_expr_width {
                    Some(1) => clz::clz1(self, es, tyvar),
                    Some(8) => clz::clz8(self, es, tyvar),
                    Some(16) => clz::clz16(self, es, tyvar),
                    Some(32) => clz::clz32(self, es, tyvar),
                    Some(64) => clz::clz64(self, es, tyvar),
                    Some(w) => unreachable!("Unexpected CLZ width {}", w),
                    None => unreachable!("Need static CLZ width"),
                }
            }
            Expr::A64CLZ(ty, e) => {
                let tyvar = *tyvar.unwrap();
                let es = self.vir_expr_to_sexp(*e);
                let val = self.get_expr_value(&*ty);
                match val {
                    Some(32) => clz::clz32(self, es, tyvar),
                    Some(64) => clz::clz64(self, es, tyvar),
                    Some(w) => {
                        println!("Unexpected A64CLZ width {}", w);
                        self.additional_assumptions.push(self.smt.false_());
                        es
                    }
                    None => {
                        println!("Need static A64CLZ width");
                        self.additional_assumptions.push(self.smt.false_());
                        es
                    }
                }
            }
            Expr::CLS(e) => {
                let tyvar = *tyvar.unwrap();
                let es = self.vir_expr_to_sexp(*e);
                match static_expr_width {
                    Some(1) => cls::cls1(self, tyvar),
                    Some(8) => cls::cls8(self, es, tyvar),
                    Some(16) => cls::cls16(self, es, tyvar),
                    Some(32) => cls::cls32(self, es, tyvar),
                    Some(64) => cls::cls64(self, es, tyvar),
                    Some(w) => unreachable!("Unexpected CLS width {}", w),
                    None => unreachable!("Need static CLS width"),
                }
            }
            Expr::A64CLS(ty, e) => {
                let tyvar = *tyvar.unwrap();
                let es = self.vir_expr_to_sexp(*e);
                let val = self.get_expr_value(&*ty);
                match val {
                    Some(32) => cls::a64cls32(self, es, tyvar),
                    Some(64) => cls::cls64(self, es, tyvar),
                    Some(w) => {
                        println!("Unexpected A64CLS width {}", w);
                        self.additional_assumptions.push(self.smt.false_());
                        es
                    }
                    None => {
                        println!("Need static A64CLS width");
                        self.additional_assumptions.push(self.smt.false_());
                        es
                    }
                }
            }
            Expr::Rev(e) => {
                let tyvar = *tyvar.unwrap();
                let es = self.vir_expr_to_sexp(*e);
                match static_expr_width {
                    Some(1) => rev::rev1(self, es, tyvar),
                    Some(8) => rev::rev8(self, es, tyvar),
                    Some(16) => rev::rev16(self, es, tyvar),
                    Some(32) => rev::rev32(self, es, tyvar),
                    Some(64) => rev::rev64(self, es, tyvar),
                    Some(w) => unreachable!("Unexpected CLS width {}", w),
                    None => unreachable!("Need static CLS width"),
                }
            }
            Expr::A64Rev(ty, e) => {
                let tyvar = *tyvar.unwrap();
                let es = self.vir_expr_to_sexp(*e);
                let val = self.get_expr_value(&*ty);
                match val {
                    Some(32) => rev::rbit32(self, es, tyvar),
                    Some(64) => rev::rev64(self, es, tyvar),
                    Some(w) => {
                        println!("Unexpected A64Rev width {}", w);
                        self.additional_assumptions.push(self.smt.false_());
                        es
                    }
                    None => {
                        println!("Need static A64Rev width");
                        self.additional_assumptions.push(self.smt.false_());
                        es
                    }
                }
            }
        }
    }

    // Checks whether the assumption list is always false
    fn check_assumptions_feasibility(&mut self, assumptions: &Vec<SExpr>) -> bool {
        println!("Checking assumption feasibility");
        self.smt.push().unwrap();
        for a in assumptions {
            debug!("{}", self.smt.display(*a));
            self.smt.assert(*a).unwrap();

            // Uncomment to debug specific asserts
            // solver.push(2).unwrap();
            // let _ = match solver.check() {
            //     Ok(Response::Sat) => {
            //         println!("Assertion list is feasible");
            //         true
            //     }
            //     Ok(Response::Unsat) => {
            //         println!("Assertion list is infeasible!");
            //         panic!();
            //         false
            //     }
            //     Err(err) => {
            //         unreachable!("Error! {:?}", err);
            //     }
            // };
            // solver.pop(2).unwrap();
        }
        let res = match self.smt.check() {
            Ok(Response::Sat) => {
                println!("Assertion list is feasible");
                true
            }
            Ok(Response::Unsat) => {
                println!("Assertion list is infeasible!");
                false
            }
            Ok(Response::Unknown) => {
                panic!("Solver said 'unk'");
            }
            Err(err) => {
                unreachable!("Error! {:?}", err);
            }
        };
        self.smt.pop().unwrap();
        res
    }

    fn display_hex_to_bin(&self, value: SExpr) -> String {
        let sexpr_hex_prefix = "#x";
        let val_str = self.smt.display(value).to_string();
        if val_str.starts_with(sexpr_hex_prefix) {
            let without_prefix = val_str.trim_start_matches("#x");
            let as_unsigned = u64::from_str_radix(without_prefix, 16).unwrap();
            format!("{}\n{:#b}", self.smt.display(value), as_unsigned)
        } else {
            val_str
        }
    }

    fn display_value(&self, variable: SExpr, value: SExpr) -> (String, String) {
        let var_str = self.smt.display(variable).to_string();
        (var_str, self.display_hex_to_bin(value))
    }

    fn display_model(&mut self) {
        println!("Quantified variables:");
        let mut vars = vec![];
        for (name, atom) in &self.var_map {
            let solution = self
                .smt
                .get_value(vec![self.smt.atom(name), *atom])
                .unwrap();
            for (variable, value) in solution {
                vars.push(self.display_value(variable, value));
            }
        }
        for (name, _) in &self.additional_decls {
            let solution = self.smt.get_value(vec![self.smt.atom(name)]).unwrap();
            for (variable, value) in solution {
                vars.push(self.display_value(variable, value));
            }
        }
        vars.sort_by_key(|x| x.0.clone());
        vars.dedup();
        for (v, x) in vars {
            println!("{}", v);
            println!("{}\n", x);
        }
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
pub fn run_solver(rule_sem: RuleSemantics) -> VerificationResult {
    let solver = easy_smt::ContextBuilder::new()
        .solver("z3", ["-smt2", "-in"])
        .build()
        .unwrap();

    let mut assumptions: Vec<SExpr> = vec![];

    let mut ctx = SolverCtx {
        smt: solver,
        tyctx: rule_sem.tyctx,
        bitwidth: REG_WIDTH,
        var_map: HashMap::new(),
        width_vars: HashMap::new(),
        width_assumptions: vec![],
        additional_decls: vec![],
        additional_assumptions: vec![],
        fresh_bits_idx: 0,
    };

    for (_e, t) in &ctx.tyctx.tyvars {
        // dbg!(t);
        // dbg!(&_e);
        let ty = &ctx.tyctx.tymap[&t];
        match ty {
            Type::BitVector(w) => {
                let width_name = format!("width__{}", t);
                ctx.additional_decls
                    .push((width_name.clone(), ctx.smt.int_sort()));
                match *w {
                    Some(bitwidth) => {
                        ctx.width_assumptions.push(
                            ctx.smt
                                .eq(ctx.smt.atom(&width_name), ctx.smt.numeral(bitwidth)),
                        );
                    }
                    None => {
                        dbg!(_e);
                        panic!("Resolve all widths!")
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
        let var_ty = ctx.vir_to_smt_ty(&ty);
        println!("\t{} : {}", name, ctx.smt.display(var_ty));
        if let Type::BitVector(w) = ty {
            let wide = ctx.widen_to_query_width(
                v.tyvar,
                w.unwrap_or(ctx.bitwidth),
                ctx.smt.atom(name),
                Some(name.to_string()),
            );
            ctx.var_map.insert(name.clone(), wide);
        }
        ctx.smt.declare_const(name, var_ty).unwrap();
    }

    println!("Adding explicit assumptions");
    for a in &rule_sem.assumptions {
        let p = ctx.vir_expr_to_sexp(a.clone());
        assumptions.push(p)
    }
    println!("Adding width assumptions");
    for a in &ctx.width_assumptions {
        assumptions.push(a.clone());
    }
    println!("Adding additional assumptions");
    for a in &ctx.additional_assumptions {
        assumptions.push(a.clone());
    }

    println!("Declaring additional variables");
    for (name, ty) in &ctx.additional_decls {
        println!("\t{} : {}", name, ctx.smt.display(*ty));
        ctx.smt.declare_const(name, *ty).unwrap();
    }

    // Check whether the assumptions are possible
    if !ctx.check_assumptions_feasibility(&assumptions) {
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

    let lhs = ctx.vir_expr_to_sexp(rule_sem.lhs);
    let rhs = ctx.vir_expr_to_sexp(rule_sem.rhs);

    let lhs_care_bits = ctx.smt.extract((width - 1).try_into().unwrap(), 0, lhs);
    let rhs_care_bits = ctx.smt.extract((width - 1).try_into().unwrap(), 0, rhs);

    let side_equality = ctx.smt.eq(lhs_care_bits, rhs_care_bits);
    println!(
        "LHS and RHS equality condition:\n\t{}\n",
        ctx.smt.display(side_equality)
    );

    let assumption_conjunction = ctx.smt.and_many(assumptions);
    let query = ctx
        .smt
        .not(ctx.smt.imp(assumption_conjunction, side_equality));
    println!("Running query");
    ctx.smt.assert(query).unwrap();

    match ctx.smt.check() {
        Ok(Response::Sat) => {
            println!("Verification failed");
            ctx.display_model();
            VerificationResult::Failure(Counterexample {})
        }
        Ok(Response::Unsat) => {
            println!("Verification succeeded");
            VerificationResult::Success
        }
        Ok(Response::Unknown) => {
            panic!("Solver said 'unk'");
        }
        Err(err) => {
            unreachable!("Error! {:?}", err);
        }
    }
}
