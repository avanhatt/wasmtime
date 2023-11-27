use crate::annotations::AnnotationEnv;
use cranelift_isle::sema::{TermEnv, TypeEnv};
use std::collections::HashMap;
use veri_ir::TermSignature;

pub fn isle_inst_types(
    termenv: &TermEnv,
    typeenv: &TypeEnv,
    annotation_env: &AnnotationEnv,
) -> HashMap<String, Vec<TermSignature>> {
    let mut inst_types = HashMap::new();

    // Populate from ISLE.
    for (term_id, term_sigs) in &annotation_env.instantiations_map {
        let sym = termenv.terms[term_id.index()].name;
        let name = typeenv.syms[sym.index()].clone();
        inst_types.insert(name, term_sigs.clone());
    }

    inst_types
}
