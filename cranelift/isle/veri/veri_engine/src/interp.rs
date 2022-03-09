/// Interpret and build an assumption context from the LHS and RHS of rules.
use crate::isle_annotations::isle_annotation_for_term;
use crate::renaming::rename_annotation_vars;
use veri_ir::{BoundVar, VIRAnnotation, VIRExpr, VIRType};

use std::collections::HashMap;
use std::fmt::Debug;

use cranelift_isle as isle;
use isle::sema::{Pattern, TermArgPattern, TermEnv, TypeEnv, TypeId, VarId};

/// Get the Clif ISLE type name
fn clif_type_name(typeid: TypeId, typeenv: &TypeEnv) -> String {
    match &typeenv.types[typeid.index()] {
        &isle::sema::Type::Primitive(_, sym, _) | &isle::sema::Type::Enum { name: sym, .. } => {
            typeenv.syms[sym.index()].clone()
        }
    }
}

/// An approximation for now: types from CLIF type names
fn vir_type_for_clif_ty(base_ty: &VIRType, clif: &str) -> VIRType {
    match clif {
        "Type" => VIRType::IsleType,
        "Reg" => base_ty.clone(),
        _ => unimplemented!(),
    }
}

/// Trait defining how to produce an verification IR expression from an
/// ISLE term, used to recursively interpret terms on both the LHS and RHS.
trait ToVIRExpr {
    fn to_expr(
        &self,
        ctx: &mut AssumptionContext,
        termenv: &TermEnv,
        typeenv: &TypeEnv,
        ty: &VIRType,
    ) -> VIRExpr;

    fn type_id(&self) -> TypeId;
}

/// Type for term arguments for ISLE LHS terms.
impl ToVIRExpr for TermArgPattern {
    fn to_expr(
        &self,
        ctx: &mut AssumptionContext,
        termenv: &TermEnv,
        typeenv: &TypeEnv,
        ty: &VIRType,
    ) -> VIRExpr {
        match self {
            TermArgPattern::Pattern(pat) => ctx.interp_pattern(pat, termenv, typeenv, ty),
            _ => unimplemented!("{:?}", self),
        }
    }

    fn type_id(&self) -> TypeId {
        match self {
            TermArgPattern::Expr(e) => e.type_id(),
            TermArgPattern::Pattern(p) => p.ty(),
        }
    }
}

/// Type for term arguments for ISLE RHS terms.
impl ToVIRExpr for isle::sema::Expr {
    fn to_expr(
        &self,
        ctx: &mut AssumptionContext,
        termenv: &TermEnv,
        typeenv: &TypeEnv,
        ty: &VIRType,
    ) -> VIRExpr {
        ctx.interp_sema_expr(self, termenv, typeenv, ty)
    }

    fn type_id(&self) -> TypeId {
        self.ty()
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
#[derive(Clone, Debug)]
pub struct AssumptionContext {
    pub quantified_vars: Vec<BoundVar>,
    pub assumptions: Vec<Assumption>,
    pub var_map: HashMap<VarId, BoundVar>,

    // Add int suffix to maintain unique identifiers
    ident_map: HashMap<String, i32>,

    // Yet-to-be-define uninterpreted functions
    undefined_funcs: Vec<String>,
}

impl AssumptionContext {
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
        a: &VIRAnnotation,
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

    fn get_annotation_for_term(&mut self, term: &str, ty: &VIRType) -> Option<VIRAnnotation> {
        if let Some(initial_annotation) = isle_annotation_for_term(term, ty) {
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
        term_name: &str,
        subterms: Vec<T>,
        termenv: &TermEnv,
        typeenv: &TypeEnv,
        ty: &VIRType,
    ) -> VIRExpr {
        if let Some(annotation) = self.get_annotation_for_term(term_name, ty) {
            // The annotation should have the same number of arguments as given here
            assert_eq!(subterms.len(), annotation.func().args.len());

            for (arg, subterm) in annotation.func().args.iter().zip(subterms) {
                let subexpr = subterm.to_expr(self, termenv, typeenv, &arg.ty);
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
            self.undefined_funcs.push(term_name.to_string());

            // If we don't have an annotation for the term, treat it as an uninterpreted
            // function
            // NOTE: for now, we get subterm types based on matching on ISLE type names.
            let mut args = vec![];
            for subterm in subterms.iter() {
                let arg_clif_ty = clif_type_name(subterm.type_id(), typeenv);
                let vir_ty = vir_type_for_clif_ty(ty, &arg_clif_ty);
                let subexpr = subterm.to_expr(self, termenv, typeenv, &vir_ty);
                args.push(subexpr);
            }
            let func_ty = VIRType::Function(
                args.iter().map(|a| a.ty().clone()).collect(),
                Box::new(ty.clone()),
            );
            let func = BoundVar::new(term_name, &func_ty);
            ty.apply(func.as_expr(), args)

            // TODO: branching vs OR for multiple matching rules?
            // eventually: might be cool to choose based on number
            //     specializing this could be _before_ the SMT
            //     often will be mutually exclusive
            //      3rd option: morally the same thing: do conceptual inlining at the IR level first
        }
    }

    fn interp_pattern(
        &mut self,
        bvpat: &Pattern,
        termenv: &TermEnv,
        typeenv: &TypeEnv,
        ty: &VIRType,
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
            Pattern::And(_, children) => {
                // The `and` construct requires all subpatterns match. For now, encode
                // as each subpattern producing the same equivalent expr result.
                let subpattern_exprs: Vec<VIRExpr> = children
                    .iter()
                    .map(|p| self.interp_pattern(p, termenv, typeenv, ty))
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

    pub fn interp_sema_expr(
        &mut self,
        expr: &isle::sema::Expr,
        termenv: &TermEnv,
        typeenv: &TypeEnv,
        ty: &VIRType,
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
        ty: &VIRType,
    ) -> VIRExpr {
        self.interp_pattern(pattern, termenv, typeenv, ty)
    }

    /// Construct the term environment from the AST and the type environment.
    pub fn from_lhs(
        lhs: &Pattern,
        termenv: &TermEnv,
        typeenv: &TypeEnv,
        ty: &VIRType,
    ) -> (AssumptionContext, VIRExpr) {
        let mut ctx = AssumptionContext {
            quantified_vars: vec![],
            assumptions: vec![],
            var_map: HashMap::new(),
            ident_map: HashMap::new(),
            undefined_funcs: vec![],
        };
        let expr = ctx.lhs_to_assumptions(lhs, termenv, typeenv, ty);
        (ctx, expr)
    }
}
