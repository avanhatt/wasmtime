use veri_engine_lib::interp::AssumptionContext;
use veri_engine_lib::rule_tree::verify_rules_for_type_with_lhs_root;
use veri_engine_lib::solver::run_solver_single_rule;
use cranelift_isle as isle;
use isle::sema::{Rule, TermEnv, TypeEnv};
use veri_annotation::parser_wrapper::{parse_annotations_str, AnnotationEnv};
use veri_ir::{all_starting_bitvectors, VIRType, VerificationResult};

#[cfg(test)]
fn verify_rule_for_type(
    rule: &Rule,
    termenv: &TermEnv,
    typeenv: &TypeEnv,
    annotation_env: &AnnotationEnv,
    ty: &VIRType,
) -> VerificationResult {
    // For now, starting types must be bitvectors
    assert!(ty.is_bv());
    let mut ctx = AssumptionContext::new(termenv, typeenv, annotation_env, ty);
    let rule_semantics = ctx.interp_rule(rule);
    run_solver_single_rule(rule_semantics, ty)
}


pub fn foo () {
    panic!()
}
