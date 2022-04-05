use crate::renaming::rename_annotation_vars;
/// Interpret and build an assumption context from the LHS and RHS of rules.
use crate::type_check::TypeContext;
use veri_ir::{BoundVar, VIRExpr, VIRTermAnnotation, VIRType, RuleSemantics};
use veri_annotation::parser_wrapper::{AnnotationEnv};

use std::{collections::HashMap};
use std::fmt::Debug;

use cranelift_isle as isle;
use isle::sema::{Pattern, TermArgPattern, TermEnv, TermId, TypeEnv, TypeId, VarId};

/// Trait defining how to produce an verification IR expression from an
/// ISLE term, used to recursively interpret terms on both the LHS and RHS.
trait ToVIRExpr {
    fn to_expr(&self, ctx: &mut AssumptionContext, ty: &VIRType) -> VIRExpr;

    fn type_id(&self) -> TypeId;

    fn add_undefined_term(term: &BoundVar, ctx: &mut AssumptionContext);
}

/// Type for term arguments for ISLE LHS terms.
impl ToVIRExpr for TermArgPattern {
    fn to_expr(&self, ctx: &mut AssumptionContext, ty: &VIRType) -> VIRExpr {
        match self {
            TermArgPattern::Pattern(pat) => ctx.interp_pattern(pat, ty),
            _ => unimplemented!("{:?}", self),
        }
    }

    fn type_id(&self) -> TypeId {
        match self {
            TermArgPattern::Expr(e) => e.type_id(),
            TermArgPattern::Pattern(p) => p.ty(),
        }
    }

    fn add_undefined_term(term: &BoundVar, ctx: &mut AssumptionContext) {
        ctx.lhs_undefined_terms.push(term.clone())
    }
}

/// Type for term arguments for ISLE RHS terms.
impl ToVIRExpr for isle::sema::Expr {
    fn to_expr(&self, ctx: &mut AssumptionContext, ty: &VIRType) -> VIRExpr {
        ctx.interp_sema_expr(self, ty)
    }

    fn type_id(&self) -> TypeId {
        self.ty()
    }

    fn add_undefined_term(term: &BoundVar, ctx: &mut AssumptionContext) {
        ctx.rhs_undefined_terms.push(term.clone())
    }
}

/// Assumption consist of single verification IR expressions, which must have
/// boolean type.
#[derive(Clone, Debug)]
pub struct Assumption {
    assume: VIRExpr,
}

impl Assumption {
    /// Create a new assumption, checking type.
    pub fn new(assume: VIRExpr) -> Self {
        assert!(assume.ty().is_bool());
        Self { assume }
    }

    /// Get the assumption as an expression.
    pub fn assume(&self) -> &VIRExpr {
        &self.assume
    }
}
pub struct AssumptionContext<'ctx> {
    pub quantified_vars: Vec<BoundVar>,
    pub assumptions: Vec<Assumption>,
    pub var_map: HashMap<VarId, BoundVar>,

    // Pointers to ISLE environments
    termenv: &'ctx TermEnv,
    typeenv: &'ctx TypeEnv,

    // Add int suffix to maintain unique identifiers
    ident_map: HashMap<String, i32>,

    // Yet-to-be-define uninterpreted functions
    lhs_undefined_terms: Vec<BoundVar>,
    rhs_undefined_terms: Vec<BoundVar>,

    // For type checking
    type_ctx: TypeContext<'ctx>,
}

impl<'ctx> AssumptionContext<'ctx> {
    /// Get a new identifier starting with a root ID (adds a unique suffix)
    fn new_ident(&mut self, root: &str) -> String {
        let idx = self.ident_map.entry(root.to_string()).or_insert(0);
        *idx += 1;
        format!("{}{}", root, idx)
    }

    /// Produce a new bound variable with unique name, and add it to our quantified variables
    fn new_var(&mut self, root: &str, ty: &VIRType, varid: &VarId) -> BoundVar {
        let ident = self.new_ident(root);
        let var = BoundVar::new(&ident, ty);
        self.var_map.insert(*varid, var.clone());
        self.quantified_vars.push(var.clone());
        var
    }

    fn build_annotation_remapping(
        &mut self,
        a: &VIRTermAnnotation,
        term: &str,
    ) -> HashMap<String, String> {
        let mut renaming_map: HashMap<String, String> = HashMap::new();
        for b in &a.func().args {
            renaming_map.insert(
                b.name.clone(),
                self.new_ident(&format!("{}_{}", term, &b.name)).clone(),
            );
        }
        renaming_map.insert(
            a.func().ret.name.clone(),
            self.new_ident(&format!("{}_{}", term, a.func().ret.name)),
        );
        renaming_map
    }

    fn get_annotation_for_term(
        &mut self,
        term: &str,
        subterm_typeids: Vec<TypeId>,
        ty: &VIRType,
    ) -> Option<VIRTermAnnotation> {
        if let Some(initial_annotation) =
            self.type_ctx
                .typed_isle_annotation_for_term(term, subterm_typeids, ty)
        {
            // Build renaming map from bound vars in the signature
            let read_renames = self.build_annotation_remapping(&initial_annotation, term);
            // Read-only renaming map closure
            let rename = |v: &BoundVar| {
                let id = read_renames.get(&v.name.clone()).unwrap();
                BoundVar {
                    name: id.to_string(),
                    ty: v.ty.clone(),
                }
            };
            Some(rename_annotation_vars(initial_annotation, rename))
        } else {
            None
        }
    }

    fn interp_term_with_subexprs<T: ToVIRExpr + Debug>(
        &mut self,
        termid: &TermId,
        subterms: Vec<T>,
        ty: &VIRType,
    ) -> VIRExpr {
        let term = &self.termenv.terms[termid.index()];
        let term_name = &self.typeenv.syms[term.name.index()];
        let subterm_typeids: Vec<TypeId> = subterms.iter().map(|t| t.type_id()).collect();
        if let Some(annotation) = self.get_annotation_for_term(term_name, subterm_typeids, ty) {
            // The annotation should have the same number of arguments as given here
            assert_eq!(subterms.len(), annotation.func().args.len());

            for (arg, subterm) in annotation.func().args.iter().zip(subterms) {
                let subexpr = subterm.to_expr(self, &arg.ty);
                self.assumptions.push(Assumption::new(VIRType::eq(
                    subexpr,
                    VIRExpr::Var(arg.clone()),
                )));
                self.quantified_vars.push(arg.clone());
            }
            for a in annotation.assertions() {
                self.assumptions.push(Assumption::new(a.clone()));
            }
            self.quantified_vars.push(annotation.func().ret.clone());
            annotation.func().ret.as_expr()
        } else {
            // If we don't have an annotation for the term, treat it as an uninterpreted
            // function
            // NOTE: for now, we get subterm types based on matching on ISLE type names.
            let mut args = vec![];
            for subterm in subterms.iter() {
                let vir_ty = self.type_ctx.vir_type_for_type_id(subterm.type_id());
                let subexpr = subterm.to_expr(self, &vir_ty);
                args.push(subexpr);
            }
            let func_ty = VIRType::Function(
                args.iter().map(|a| a.ty().clone()).collect(),
                Box::new(ty.clone()),
            );
            let func = BoundVar::new(term_name, &func_ty);
            
            // Add to our list of undefined terms for this side
            T::add_undefined_term(&func, self);

            ty.apply(func.as_expr(), args)
        }
    }

    fn interp_pattern(&mut self, bvpat: &Pattern, ty: &VIRType) -> VIRExpr {
        match bvpat {
            // If we hit a bound wildcard, then the bound variable has no assumptions
            Pattern::BindPattern(_, varid, subpat) => match **subpat {
                Pattern::Wildcard(..) => VIRExpr::Var(self.new_var("x", ty, varid)),
                _ => unimplemented!("Unexpected BindPattern {:?}", subpat),
            },
            Pattern::Term(_, termid, arg_patterns) => {
                self.interp_term_with_subexprs(termid, arg_patterns.to_vec(), ty)
            }
            Pattern::And(_, children) => {
                // The `and` construct requires all subpatterns match. For now, encode
                // as each subpattern producing the same equivalent expr result.
                let subpattern_exprs: Vec<VIRExpr> = children
                    .iter()
                    .map(|p| self.interp_pattern(p, ty))
                    .collect();

                // We assert all subexpressions are equivalent to the first subexpression,
                // then return it.
                let first = subpattern_exprs[0].clone();
                for (i, e) in subpattern_exprs.iter().enumerate() {
                    if i != 0 {
                        self.assumptions
                            .push(Assumption::new(VIRType::eq(first.clone(), e.clone())));
                    }
                }
                first
            }
            _ => unimplemented!("{:?}", bvpat),
        }
    }

    pub fn interp_sema_expr(&mut self, expr: &isle::sema::Expr, ty: &VIRType) -> VIRExpr {
        match expr {
            isle::sema::Expr::Term(_, termid, subterms) => {
                self.interp_term_with_subexprs(termid, subterms.to_vec(), ty)
            }
            isle::sema::Expr::Var(_, varid) => {
                let bound_var = self.var_map.get(varid).unwrap();
                bound_var.ty.bv_var(bound_var.name.clone())
            }
            _ => unimplemented!(),
        }
    }

    /// Takes in LHS definitions, ty map, produces SMTLIB list
    fn lhs_to_assumptions(&mut self, pattern: &Pattern, ty: &VIRType) -> VIRExpr {
        self.interp_pattern(pattern, ty)
    }

    /// Construct the term environment from the AST and the type environment.
    pub fn from_lhs(
        lhs: &Pattern,
        termenv: &'ctx TermEnv,
        typeenv: &'ctx TypeEnv,
        annotation_env: &'ctx AnnotationEnv,
        ty: &VIRType,
    ) -> (AssumptionContext<'ctx>, VIRExpr) {
        let mut ctx = AssumptionContext {
            quantified_vars: vec![],
            assumptions: vec![],
            termenv,
            typeenv,
            var_map: HashMap::new(),
            ident_map: HashMap::new(),
            lhs_undefined_terms: vec![],
            rhs_undefined_terms: vec![],
            type_ctx: TypeContext::new(typeenv, annotation_env, ty.clone()),
        };
        let expr = ctx.lhs_to_assumptions(lhs, ty);
        (ctx, expr)
    }

    pub fn interp_rule(
        rule: &isle::sema::Rule,
        termenv: &TermEnv,
        typeenv: &TypeEnv,
        annotation_env: &AnnotationEnv,
        ty: &VIRType,
    ) -> RuleSemantics {
        let (mut assumption_ctx, lhs) = AssumptionContext::from_lhs(&rule.lhs, termenv, typeenv, annotation_env, ty);
        let rhs = assumption_ctx.interp_sema_expr(&rule.rhs, ty);
        RuleSemantics {
            lhs, 
            rhs,
            assumptions: assumption_ctx.assumptions.iter().map(|a| a.assume().clone()).collect(), 
            quantified_vars: assumption_ctx.quantified_vars.clone(),
            lhs_undefined_terms: assumption_ctx.lhs_undefined_terms, 
            rhs_undefined_terms: assumption_ctx.rhs_undefined_terms,
        }
    }
}
