use crate::renaming::rename_annotation_vars;
/// Interpret and build an assumption context from the LHS and RHS of rules.
use crate::type_check::TypeContext;
use veri_annotation::parser_wrapper::AnnotationEnv;
use veri_ir::{BoundVar, RuleSemantics, UndefinedTerm, VIRExpr, VIRTermAnnotation, VIRType};

use std::collections::HashMap;
use std::fmt::Debug;

use cranelift_isle as isle;
use isle::sema::{Expr, Pattern, TermEnv, TermId, TypeEnv, TypeId, VarId};

/// Trait defining how to produce an verification IR expression from an
/// ISLE term, used to recursively interpret terms on both the LHS and RHS.
trait ToVIRExpr {
    fn to_expr(&self, ctx: &mut AssumptionContext, ty: &VIRType) -> VIRExpr;

    fn type_id(&self) -> TypeId;

    fn add_undefined_term(term: UndefinedTerm, ctx: &mut AssumptionContext);
}

/// Type for term arguments for ISLE LHS terms.
impl ToVIRExpr for Pattern {
    fn to_expr(&self, ctx: &mut AssumptionContext, ty: &VIRType) -> VIRExpr {
        ctx.interp_pattern(self, ty)
    }

    fn type_id(&self) -> TypeId {
        self.ty()
    }

    fn add_undefined_term(term: UndefinedTerm, ctx: &mut AssumptionContext) {
        assert!(
            !ctx.lhs_undefined_terms.contains_key(&term.name),
            "Duplicate undefined terms on LHS currently unsupported: {}",
            term.name
        );
        ctx.lhs_undefined_terms.insert(term.name.clone(), term);
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

    fn add_undefined_term(term: UndefinedTerm, ctx: &mut AssumptionContext) {
        assert!(
            !ctx.rhs_undefined_terms.contains_key(&term.name),
            "Duplicate undefined terms on RHS currently unsupported: {}",
            term.name
        );
        ctx.rhs_undefined_terms.insert(term.name.clone(), term);
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
    lhs_undefined_terms: HashMap<String, UndefinedTerm>,
    rhs_undefined_terms: HashMap<String, UndefinedTerm>,

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
    fn new_var(&mut self, root: &str, ty: &VIRType) -> BoundVar {
        let ident = self.new_ident(root);
        let var = BoundVar::new(&ident, ty);
        // self.var_map.insert(*varid, var.clone());
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
        println!("Interpreting term: {}", term_name);
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

            let ret = self.new_var(term_name, ty);
            let undef = UndefinedTerm {
                name: term_name.to_string(),
                ret,
                args,
            };
            // Add to our list of undefined terms for this side
            T::add_undefined_term(undef.clone(), self);
            VIRExpr::UndefinedTerm(undef)
        }
    }

    fn interp_pattern(&mut self, bvpat: &Pattern, ty: &VIRType) -> VIRExpr {
        match bvpat {
            // If we hit a bound wildcard, then the bound variable has no assumptions
            Pattern::BindPattern(_, varid, subpat) => match **subpat {
                Pattern::Wildcard(..) => {
                    let var = self.new_var("x", ty);
                    self.var_map.insert(*varid, var.clone());
                    VIRExpr::Var(var)
                }
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
            Expr::Term(_, termid, subterms) => {
                self.interp_term_with_subexprs(termid, subterms.to_vec(), ty)
            }
            Expr::Var(_, varid) => {
                let bound_var = self.var_map.get(varid).unwrap();
                bound_var.ty.bv_var(bound_var.name.clone())
            }
            Expr::ConstInt(_, v) => VIRExpr::Const(ty.clone(), *v as i128),
            Expr::ConstPrim(_, sym) => {
                let name = &self.typeenv.syms[sym.index()];
                match name.as_str() {
                    "I64" => VIRExpr::Const(VIRType::Int, 64),
                    "I32" => VIRExpr::Const(VIRType::Int, 64),
                    _ => todo!("{:?}", &name),
                }
            }
            Expr::Let { bindings, body, .. } => {
                for (varid, _tyid, expr) in bindings {
                    let to_bind = self.interp_sema_expr(expr, ty);
                    let var = self.new_var("let", to_bind.ty());
                    self.var_map.insert(*varid, var.clone());
                    self.assumptions
                        .push(Assumption::new(VIRType::eq(var.as_expr(), to_bind)));
                }
                self.interp_sema_expr(body, ty)
            }
        }
    }

    /// Takes in LHS definitions, ty map, produces SMTLIB list
    fn lhs_to_assumptions(&mut self, pattern: &Pattern, ty: &VIRType) -> VIRExpr {
        self.interp_pattern(pattern, ty)
    }

    pub fn new(
        termenv: &'ctx TermEnv,
        typeenv: &'ctx TypeEnv,
        annotation_env: &'ctx AnnotationEnv,
        ty: &VIRType,
    ) -> AssumptionContext<'ctx> {
        AssumptionContext {
            quantified_vars: vec![],
            assumptions: vec![],
            termenv,
            typeenv,
            var_map: HashMap::new(),
            ident_map: HashMap::new(),
            lhs_undefined_terms: HashMap::new(),
            rhs_undefined_terms: HashMap::new(),
            type_ctx: TypeContext::new(typeenv, annotation_env, ty.clone()),
        }
    }

    pub fn interp_rule(&mut self, rule: &isle::sema::Rule) -> RuleSemantics {
        let ty = self.type_ctx.ty.clone();
        let lhs = self.lhs_to_assumptions(&rule.lhs, &ty);
        let rhs = self.interp_sema_expr(&rule.rhs, &ty);

        // Drain rule-specific fields (TODO: make this cleaner)
        let assumptions = self
            .assumptions
            .drain(..)
            .map(|a| a.assume().clone())
            .collect();
        let quantified_vars = self.quantified_vars.drain(..).collect();
        let lhs_undefined_terms = self.lhs_undefined_terms.drain().map(|(_, t)| t).collect();
        let rhs_undefined_terms = self.rhs_undefined_terms.drain().map(|(_, t)| t).collect();

        RuleSemantics {
            lhs,
            rhs,
            assumptions,
            quantified_vars,
            lhs_undefined_terms,
            rhs_undefined_terms,
        }
    }
}
