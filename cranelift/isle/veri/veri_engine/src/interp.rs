//! Interpret and build an assumption context from the left hand side of a rule.
//!

use crate::isle_annotations::{isle_annotation_for_term, rename_annotation_vars};
use veri_ir::{BoundVar, VIRAnnotation, VIRExpr, VIRType};

use std::collections::HashMap;

use cranelift_isle as isle;
use isle::sema::{Pattern, TermArgPattern, TermEnv, TypeEnv, VarId};

trait ToVIRExpr {
    fn to_expr(
        &self,
        ctx: &mut AssumptionContext,
        termenv: &TermEnv,
        typeenv: &TypeEnv,
        ty: VIRType,
    ) -> VIRExpr;
}

impl ToVIRExpr for TermArgPattern {
    fn to_expr(
        &self,
        ctx: &mut AssumptionContext,
        termenv: &TermEnv,
        typeenv: &TypeEnv,
        ty: VIRType,
    ) -> VIRExpr {
        match self {
            TermArgPattern::Pattern(pat) => ctx.interp_pattern(pat, termenv, typeenv, ty),
            _ => unimplemented!("{:?}", self),
        }
    }
}

impl ToVIRExpr for isle::sema::Expr {
    fn to_expr(
        &self,
        ctx: &mut AssumptionContext,
        termenv: &TermEnv,
        typeenv: &TypeEnv,
        ty: VIRType,
    ) -> VIRExpr {
        ctx.interp_sema_expr(self, termenv, typeenv, ty)
    }
}

#[derive(Clone, Debug)]
pub struct Assumption {
    pub assume: VIRExpr,
}

#[derive(Clone, Debug)]
pub struct AssumptionContext {
    pub quantified_vars: Vec<BoundVar>,
    pub assumptions: Vec<Assumption>,
    pub var_map: HashMap<VarId, BoundVar>,

    // Add int suffix to maintain unique identifiers
    ident_map: HashMap<String, i32>,
}

impl AssumptionContext {
    fn new_ident(&mut self, root: &str) -> String {
        let idx = self.ident_map.entry(root.to_string()).or_insert(0);
        *idx += 1;
        format!("{}{}", root, idx)
    }

    fn new_var(&mut self, root: &str, ty: VIRType, varid: &VarId) -> BoundVar {
        let ident = self.new_ident(root);
        let var = BoundVar { name: ident, ty };
        self.var_map.insert(*varid, var.clone());
        self.quantified_vars.push(var.clone());
        var
    }

    fn build_annotation_remapping(
        &mut self,
        a: &VIRAnnotation,
        term: &String,
    ) -> HashMap<String, String> {
        let mut renaming_map: HashMap<String, String> = HashMap::new();
        for b in &a.func.args {
            renaming_map.insert(
                b.name.clone(),
                self.new_ident(&format!("{}_{}", term, &b.name)).clone(),
            );
        }
        renaming_map.insert(
            a.func.result.name.clone(),
            self.new_ident(&format!("{}_{}", term, a.func.result.name))
                .clone(),
        );
        renaming_map
    }

    fn get_annotation_for_term(&mut self, term: &String, ty: VIRType) -> VIRAnnotation {
        let initial_annotation = isle_annotation_for_term(term, ty);
        // Build renaming map from bound vars in the signature
        let read_renames = self.build_annotation_remapping(&initial_annotation, term);
        // Read-only renaming map closure
        let rename = |v: &BoundVar| {
            let id = read_renames.get(&v.name.clone()).unwrap();
            BoundVar {
                name: id.to_string(),
                ty: v.ty,
            }
        };
        rename_annotation_vars(initial_annotation, rename)
    }

    fn interp_term_with_subexprs<T: ToVIRExpr>(
        &mut self,
        term_name: &String,
        subterms: Vec<T>,
        termenv: &TermEnv,
        typeenv: &TypeEnv,
        ty: VIRType,
    ) -> VIRExpr {
        let annotation = self.get_annotation_for_term(term_name, ty);

        // The annotation should have the same number of arguments as given here
        assert_eq!(subterms.len(), annotation.func.args.len());

        for (arg, subterm) in annotation.func.args.iter().zip(subterms) {
            let subexpr = subterm.to_expr(self, termenv, typeenv, arg.ty);
            self.assumptions.push(Assumption {
                // The bound arg should be equal to the recursive result
                assume: VIRType::eq(subexpr, VIRExpr::Var(arg.clone())),
            });
            self.quantified_vars.push(arg.clone());
        }
        for a in annotation.assertions {
            self.assumptions.push(Assumption { assume: a });
        }
        self.quantified_vars.push(annotation.func.result.clone());
        annotation.func.result.as_expr()
    }

    fn interp_pattern(
        &mut self,
        bvpat: &Pattern,
        termenv: &TermEnv,
        typeenv: &TypeEnv,
        ty: VIRType,
    ) -> VIRExpr {
        match bvpat {
            // If we hit a bound wildcard, then the bound variable has no assumptions
            Pattern::BindPattern(_, varid, subpat) => match **subpat {
                Pattern::Wildcard(..) => VIRExpr::Var(self.new_var("x", ty, varid)),
                _ => unimplemented!("Unexpected BindPattern {:?}", subpat),
            },
            Pattern::Term(_, termid, arg_patterns) => {
                let term = &termenv.terms[termid.index()];
                let term_name = &typeenv.syms[term.name.index()];

                self.interp_term_with_subexprs(
                    term_name,
                    arg_patterns.to_vec(),
                    termenv,
                    typeenv,
                    ty,
                )
            }
            _ => unimplemented!("{:?}", bvpat),
        }
    }

    pub fn interp_sema_expr(
        &mut self,
        expr: &isle::sema::Expr,
        termenv: &TermEnv,
        typeenv: &TypeEnv,
        ty: VIRType,
    ) -> VIRExpr {
        match expr {
            isle::sema::Expr::Term(_, termid, subterms) => {
                let term = &termenv.terms[termid.index()];
                let term_name = &typeenv.syms[term.name.index()];

                self.interp_term_with_subexprs(term_name, subterms.to_vec(), termenv, typeenv, ty)
            }
            isle::sema::Expr::Var(_, varid) => {
                let bound_var = self.var_map.get(varid).unwrap();
                bound_var.ty.bv_var(bound_var.name.clone())
            }
            _ => unimplemented!(),
        }
    }

    /// Takes in LHS definitions, ty map, produces SMTLIB list
    fn lhs_to_assumptions(
        &mut self,
        pattern: &Pattern,
        termenv: &TermEnv,
        typeenv: &TypeEnv,
        ty: VIRType,
    ) -> VIRExpr {
        self.interp_pattern(&pattern, termenv, typeenv, ty)
    }

    /// Construct the term environment from the AST and the type environment.
    pub fn from_lhs(
        lhs: &Pattern,
        termenv: &TermEnv,
        typeenv: &TypeEnv,
        ty: VIRType,
    ) -> (AssumptionContext, VIRExpr) {
        let mut ctx = AssumptionContext {
            quantified_vars: vec![],
            assumptions: vec![],
            var_map: HashMap::new(),
            ident_map: HashMap::new(),
        };
        let expr = ctx.lhs_to_assumptions(lhs, termenv, typeenv, ty);
        (ctx, expr)
    }
}
