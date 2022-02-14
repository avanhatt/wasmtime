//! Interpret and build an assumption context from the left hand side of a rule.
//!

use crate::vir_ast::{BVExpr, BoolExpr, VIRType};

use std::collections::HashMap;

use cranelift_isle as isle;
use isle::sema::{Pattern, TermArgPattern, TermEnv, TypeEnv, VarId};

#[derive(Clone, Debug)]
pub struct BoundVar {
    pub name: String,
    pub ty: VIRType,
}

#[derive(Clone, Debug)]
pub struct Assumption {
    pub assume: BoolExpr,
}

#[derive(Clone, Debug)]
pub struct AssumptionContext {
    pub quantified_vars: Vec<BoundVar>,
    pub assumptions: Vec<Assumption>,
    pub var_map: HashMap<VarId, BoundVar>,
}

impl AssumptionContext {
    // Add assumptions to the context from `has_type`
    fn assumption_for_has_type(
        &mut self,
        pattern: &Pattern,
        termenv: &TermEnv,
        typeenv: &TypeEnv,
        ty: VIRType,
    ) -> bool {
        match pattern {
            Pattern::Term(tyid, termid, arg_patterns) => {
                let term = &termenv.terms[termid.index()];
                let term_name = &typeenv.syms[term.name.index()];

                // TODO: can we pull the name "ty" from this term?
                match &arg_patterns[..] {
                    [TermArgPattern::Pattern(Pattern::BindPattern(tyid, varid, subpattern))] => {
                        match **subpattern {
                            Pattern::Wildcard(..) => {
                                let var = BoundVar {
                                    name: "ty".to_string(),
                                    ty,
                                };
                                self.quantified_vars.push(var.clone());
                                self.var_map.insert(*varid, var);
                            }
                            _ => unimplemented!("Subpattern for argument to has_type"),
                        }
                    }
                    _ => unimplemented!("Argument to has_type"),
                };

                // For now, hard-code some cases we care about
                match term_name.as_ref() {
                    "fits_in_64" => match ty {
                        VIRType::BitVector(s) => {
                            if s <= 64 {
                                self.assumptions.push(Assumption {
                                    assume: BoolExpr::Eq(
                                        Box::new(ty.bv_const(s as i128)),
                                        Box::new(ty.bv_var("ty".to_string())),
                                    ),
                                });
                                return true;
                            } else {
                                println!(
                                    "Rule does not apply for bitvector type {:?}, fails {}",
                                    ty, term_name
                                );
                                return false;
                            }
                        }
                        _ => unreachable!("{:?}", ty),
                    },
                    _ => unimplemented!("Unknown subterm for `has_type`"),
                }
            }
            _ => unimplemented!("Expected 'lower' term"),
        };
    }

    fn interp_bv_pattern(
        &mut self,
        bvpat: &Pattern,
        expr: BVExpr,
        termenv: &TermEnv,
        typeenv: &TypeEnv,
    ) -> BVExpr {
        match bvpat {
            // If we hit a bound wildcard, then the bound variable has no assumptions
            Pattern::BindPattern(tyid, varid, subpat) => match **subpat {
                Pattern::Wildcard(..) => {
                    let ret = expr.clone();
                    let var = match expr {
                        BVExpr::Var(var_ty, name) => BoundVar { name, ty: var_ty },
                        _ => unreachable!("unexpected term: {:?}", expr),
                    };
                    self.var_map.insert(*varid, var.clone());
                    return ret;
                }
                _ => unimplemented!("{:?}", subpat),
            },
            Pattern::Term(tyid, termid, arg_patterns) => {
                let term = &termenv.terms[termid.index()];
                let term_name = &typeenv.syms[term.name.index()];

                let subpats: Vec<&Pattern> = arg_patterns
                    .iter()
                    .map(|a| match a {
                        TermArgPattern::Pattern(pat) => pat,
                        _ => unimplemented!("{:?}", a),
                    })
                    .collect();

                // Inline for now
                match term_name.as_str() {
                    // No op for now
                    "lower" | "fits_in_64" => {
                        assert_eq!(subpats.len(), 1);
                        return self.interp_bv_pattern(subpats[0], expr, termenv, typeenv);
                    }
                    "has_type" => {
                        assert_eq!(subpats.len(), 2);
                        return self.interp_bv_pattern(subpats[1], expr, termenv, typeenv);
                    }
                    "imm12_from_negated_value" => {
                        // *This* value's negated value fits in 12 bits
                        let ty = expr.ty();
                        let assume_fits = VIRType::bool_eq(
                            ty.bv_binary(
                                BVExpr::BVAnd,
                                ty.bv_unary(BVExpr::BVNot, ty.bv_const((2 as i128).pow(12) - 1)),
                                expr.clone(),
                            ),
                            ty.bv_const(0),
                        );
                        self.assumptions.push(Assumption {
                            assume: assume_fits,
                        });
                        assert_eq!(subpats.len(), 1);

                        // The argument must fit in a 12-bit BV
                        let bv12 = VIRType::BitVector(12);
                        let var = BoundVar {
                            // TODO: actual stable identifier index
                            name: format!("arg_{}", term_name).to_string(),
                            ty: bv12,
                        };
                        self.quantified_vars.push(var.clone());
                        let arg = self.interp_bv_pattern(
                            subpats[0],
                            bv12.bv_var(var.name.clone()),
                            termenv,
                            typeenv,
                        );
                        let width_diff = (ty.width() as i128) - 12;
                        let as_ty = if width_diff > 0 {
                            bv12.bv_extend(BVExpr::BVZeroExt, width_diff.try_into().unwrap(), arg)
                        } else if width_diff < 0 {
                            bv12.bv_extract(0, ty.width() - 1, arg)
                        } else {
                            arg
                        };
                        let res = ty.bv_unary(BVExpr::BVNeg, as_ty);
                        self.assumptions.push(Assumption {
                            assume: VIRType::bool_eq(expr, res.clone()),
                        });
                        res
                    }
                    _ => unimplemented!("{}", term_name),
                }
            }
            _ => unimplemented!("{:?}", bvpat),
        }
    }

    // This should add bound variables and assumptions to the AssumptionContext, but now
    // interpret the actual instruction
    fn interp_lhs_inst(
        &mut self,
        inst: &Pattern,
        termenv: &TermEnv,
        typeenv: &TypeEnv,
        ty: VIRType,
    ) -> BVExpr {
        match inst {
            // For now, assume all args have the same type, `ty: SMTType`
            Pattern::Term(tyid, termid, arg_patterns) => {
                let term = &termenv.terms[termid.index()];
                let term_name = &typeenv.syms[term.name.index()];
                let mut args = vec![];
                for (i, arg) in arg_patterns.iter().enumerate() {
                    // Create new bound variable
                    let var = BoundVar {
                        name: format!("arg_{}", i).to_string(),
                        ty,
                    };
                    self.quantified_vars.push(var.clone());
                    match arg {
                        TermArgPattern::Pattern(pat) => args.push(self.interp_bv_pattern(
                            pat,
                            ty.bv_var(var.name.clone()),
                            termenv,
                            typeenv,
                        )),
                        _ => unimplemented!(),
                    }
                }
                match term_name.as_str() {
                    "iadd" => {
                        assert_eq!(args.len(), 2);
                        return ty.bv_binary(BVExpr::BVAdd, args[0].clone(), args[1].clone());
                    }
                    _ => unimplemented!(),
                }
            }
            _ => unimplemented!("Unimplemented pattern"),
        }
    }

    /// Takes in LHS definitions, ty map, produces SMTLIB list
    /// For now, also trying to say from (lower (... (iadd (a) (b)))), make fresh vars a b of size TYPE
    fn lhs_to_assumptions(
        &mut self,
        pattern: &Pattern,
        termenv: &TermEnv,
        typeenv: &TypeEnv,
        ty: VIRType,
    ) -> Option<BVExpr> {
        let (ty_pattern, inst_pattern) = unwrap_lower_has_type(pattern, termenv, typeenv);
        if !self.assumption_for_has_type(&ty_pattern, termenv, typeenv, ty) {
            return None;
        };
        return Some(self.interp_lhs_inst(&inst_pattern, termenv, typeenv, ty));
    }

    /// Construct the term environment from the AST and the type environment.
    pub fn from_lhs(
        lhs: &Pattern,
        termenv: &TermEnv,
        typeenv: &TypeEnv,
        ty: VIRType,
    ) -> Option<(AssumptionContext, BVExpr)> {
        let mut ctx = AssumptionContext {
            quantified_vars: vec![],
            assumptions: vec![],
            var_map: HashMap::new(),
        };
        let expr = ctx.lhs_to_assumptions(lhs, termenv, typeenv, ty);
        if let Some(expr) = expr {
            Some((ctx, expr))
        } else {
            None
        }
    }
}

/// For now, we assume the LHS of a rule matches (lower (has_type (...) (...))).
/// This function asserts that shape and returns the type and inst arguments to has_type.
/// TODO: should probably have lifetime instead of cloning
fn unwrap_lower_has_type(
    pattern: &Pattern,
    termenv: &TermEnv,
    typeenv: &TypeEnv,
) -> (Pattern, Pattern) {
    let lower_arg = match pattern {
        Pattern::Term(tyid, termid, arg_patterns) => {
            let term = &termenv.terms[termid.index()];
            // Outermost term is lower
            assert!(typeenv.syms[term.name.index()] == "lower");
            assert!(arg_patterns.len() == 1, "expected single argument to lower");
            &arg_patterns[0]
        }
        _ => panic!("Expected 'lower' term"),
    };
    match lower_arg {
        TermArgPattern::Pattern(Pattern::Term(tyid, termid, arg_patterns)) => {
            let term = &termenv.terms[termid.index()];
            // Outermost term is lower
            assert!(typeenv.syms[term.name.index()] == "has_type");
            match &arg_patterns[..] {
                [TermArgPattern::Pattern(ty_pattern), TermArgPattern::Pattern(inst_pattern)] => {
                    (ty_pattern.clone(), inst_pattern.clone())
                }
                _ => panic!("Expected has_type!"),
            }
        }
        _ => panic!("Expected 'lower' term"),
    }
}
