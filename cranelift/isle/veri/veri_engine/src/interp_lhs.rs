//! Interpret and build an assumption context from the left hand side of a rule.
//!

use crate::isle_annotations::{isle_annotation_for_term, rename_annotation_vars};
use veri_ir::{BVExpr, BoolExpr, BoundVar, VIRAnnotation, VIRType};

use std::{collections::HashMap, hash::Hash};

use cranelift_isle as isle;
use isle::sema::{Pattern, TermArgPattern, TermEnv, TypeEnv, VarId};

#[derive(Clone, Debug)]
pub struct Assumption {
    pub assume: BoolExpr,
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

    fn build_annotation_remapping(&mut self, a: &VIRAnnotation) -> HashMap<String, String> {
        let mut renaming_map: HashMap<String, String> = HashMap::new();
        for b in &a.func.args {
            renaming_map.insert(b.name.clone(), self.new_ident(&b.name).clone());
        }
        renaming_map.insert(
            a.func.result.name.clone(),
            self.new_ident(&a.func.result.name).clone(),
        );
        renaming_map
    }

    fn get_annotation_for_term(&mut self, term: &String, ty: VIRType) -> VIRAnnotation {
        let initial_annotation = isle_annotation_for_term(term, ty);
        // Build renaming map from bound vars in the signature
        let read_renames = self.build_annotation_remapping(&initial_annotation);
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

    fn interp_pattern(
        &mut self,
        bvpat: &Pattern,
        termenv: &TermEnv,
        typeenv: &TypeEnv,
        ty: VIRType,
    ) -> BVExpr {
        match bvpat {
            // If we hit a bound wildcard, then the bound variable has no assumptions
            Pattern::BindPattern(_, varid, subpat) => match **subpat {
                Pattern::Wildcard(..) => BVExpr::Var(self.new_var("x", ty, varid)),
                _ => unimplemented!("{:?}", subpat),
            },
            Pattern::Term(_, termid, arg_patterns) => {
                let term = &termenv.terms[termid.index()];
                let term_name = &typeenv.syms[term.name.index()];

                let subpats: Vec<&Pattern> = arg_patterns
                    .iter()
                    .map(|a| match a {
                        TermArgPattern::Pattern(pat) => pat,
                        _ => unimplemented!("{:?}", a),
                    })
                    .collect();

                let annotation = self.get_annotation_for_term(term_name, ty);

                // The annotation should have the same number of arguments as given here
                assert_eq!(subpats.len(), annotation.func.args.len());

                for (arg, subpat) in annotation.func.args.iter().zip(subpats) {
                    let expr = self.interp_pattern(subpat, termenv, typeenv, arg.ty);
                    self.assumptions.push(Assumption {
                        // The bound arg should be equal to the recursive result
                        assume: VIRType::bool_eq(expr, BVExpr::Var(arg.clone())),
                    });
                    self.quantified_vars.push(arg.clone());
                }
                for a in annotation.assertions {
                    self.assumptions.push(Assumption { assume: a });
                }
                self.quantified_vars.push(annotation.func.result.clone());
                annotation.func.result.as_expr()
            }
            _ => unimplemented!("{:?}", bvpat),
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
        Some(self.interp_pattern(&pattern, termenv, typeenv, ty))
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
            ident_map: HashMap::new(),
        };
        let expr = ctx.lhs_to_assumptions(lhs, termenv, typeenv, ty);
        expr.map(|expr| (ctx, expr))
    }
}
