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
    pub typesols: &'ctx HashMap<RuleId, Solution>,
}

impl<'ctx> TypeContext<'ctx> {
    pub fn new(
        typesols: &'ctx HashMap<RuleId, Solution>,
        width: usize,
    ) -> Self {
        TypeContext {
            typesols,
            width,
        }
    }
}
