use crate::renaming::rename_annotation_vars;
/// Interpret and build an assumption context from the LHS and RHS of rules.
use crate::type_check::TypeContext;
use crate::type_inference::Solution;
use veri_annotation::parser_wrapper::AnnotationEnv;
use veri_ir::{BoundVar, Expr, RuleSemantics, Type, UndefinedTerm, VIRTermAnnotation};

use std::collections::HashMap;
use std::fmt::Debug;

use cranelift_isle as isle;
use isle::sema::{Pattern, RuleId, TermEnv, TermId, TypeEnv, TypeId, VarId};

/// Assumption consist of single verification IR expressions, which must have
/// boolean type.
#[derive(Clone, Debug)]
pub struct Assumption {
    assume: Expr,
}

impl Assumption {
    /// Create a new assumption, checking type.
    pub fn new(assume: Expr) -> Self {
        // assert!(assume.ty().is_bool());
        Self { assume }
    }

    /// Get the assumption as an expression.
    pub fn assume(&self) -> &Expr {
        &self.assume
    }
}
pub struct AssumptionContext<'ctx> {
    pub quantified_vars: Vec<BoundVar>,
    pub assumptions: Vec<Assumption>,
    pub var_map: HashMap<VarId, BoundVar>,

    // For type checking
    pub typesols: &'ctx HashMap<RuleId, Solution>,
}

impl<'ctx> AssumptionContext<'ctx> {
    pub fn new(
        termenv: &'ctx TermEnv,
        typeenv: &'ctx TypeEnv,
        annotation_env: &'ctx AnnotationEnv,
        typesols: &'ctx HashMap<RuleId, Solution>,
        width: usize,
    ) -> AssumptionContext<'ctx> {
        AssumptionContext {
            quantified_vars: vec![],
            assumptions: vec![],
            var_map: HashMap::new(),
            typesols,
        }
    }
}
