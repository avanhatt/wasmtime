use std::cmp::Ordering;
use std::collections::HashMap;

use veri_ir::annotation_ir;
use veri_ir::{BoundVar, Expr, Type, VIRTermAnnotation, VIRTermSignature};

use cranelift_isle as isle;
use isle::sema::{RuleId, TypeEnv, TypeId};
use veri_annotation::parser_wrapper::AnnotationEnv;

use crate::type_inference::Solution;

pub struct TypeContext<'ctx> {
    // Default bitvector type
    pub width: usize,

    // Pointers to ISLE environments
    typeenv: &'ctx TypeEnv,

    // Isle annotations
    annotation_env: &'ctx AnnotationEnv,

    pub typesols: &'ctx HashMap<RuleId, Solution>,
}

impl<'ctx> TypeContext<'ctx> {
    pub fn new(
        typeenv: &'ctx TypeEnv,
        annotation_env: &'ctx AnnotationEnv,
        typesols: &'ctx HashMap<RuleId, Solution>,
        width: usize,
    ) -> Self {
        // assert!(ty.is_bv());
        TypeContext {
            typeenv,
            annotation_env,
            typesols,
            width,
        }
    }
}
