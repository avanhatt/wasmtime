use veri_ir::{VIRAnnotation, VIRType};

use crate::isle_annotations::isle_annotation_for_term;
use cranelift_isle as isle;
use isle::sema::{TypeEnv, TypeId};

/// Get the Clif ISLE type name
pub fn clif_type_name(typeid: TypeId, typeenv: &TypeEnv) -> String {
    match &typeenv.types[typeid.index()] {
        &isle::sema::Type::Primitive(_, sym, _) | &isle::sema::Type::Enum { name: sym, .. } => {
            typeenv.syms[sym.index()].clone()
        }
    }
}

/// An approximation for now: types from CLIF type names
pub fn vir_type_for_clif_ty(base_ty: &VIRType, clif: &str) -> VIRType {
    match clif {
        "Type" => VIRType::IsleType,
        "Reg" => base_ty.clone(),
        _ => unimplemented!(),
    }
}

pub fn typed_isle_annotation_for_term(term: &str, ty: &VIRType) -> Option<VIRAnnotation> {
    let initial_term = isle_annotation_for_term(term);
    // TODO: type check and convert term
    unimplemented!()
}
