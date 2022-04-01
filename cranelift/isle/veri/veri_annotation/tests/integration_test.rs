use std::path::PathBuf;

use veri_ir::isle_annotations::{isle_annotation_for_term};
use veri_annotation::parser_wrapper::{parse_annotations, parse_annotations_str};

#[test]
fn test_parser_single_file() {
    let annotation_env = parse_annotations(
        &vec![PathBuf::from("examples/simple.isle")]
    );
    assert_eq!(annotation_env.annotation_map.len(), 7);
    for (term, annotation) in annotation_env.annotation_map {
        let expected = isle_annotation_for_term(&term).unwrap();
        assert_eq!(expected, annotation);
    }
}

#[test]
fn test_parser_multi_file() {
    let annotation_env = parse_annotations(&vec![
        PathBuf::from("examples/simple.isle"), 
        PathBuf::from("examples/simple2.isle"),
    ]);
    assert_eq!(annotation_env.annotation_map.len(), 9);
    for (term, annotation) in annotation_env.annotation_map {
        let expected = isle_annotation_for_term(&term).unwrap();
        assert_eq!(expected, annotation);
    }
}

#[test]
fn test_parser_str() {
    let code = "
        ;; (decl (a) b SMTType) (assert (= a b) (<= a 64)))
        ;; {((a : Type) b : Type) | a = b, a.ty.width <= 64}
        ;; (decl fits_in_64 (Type) Type)
        ;;@ (spec (sig (args arg) (ret))
        ;;@     (assertions (= (arg) (ret)), (<= (arg) (64i128: isleType))))
        (decl fits_in_64 (Type) Type)
        (extern extractor fits_in_64 fits_in_64)
        
        (decl fits_in_32 (Type) Type)
        (extern extractor fits_in_32 fits_in_32)
        
        ;; (decl (a b) c bvX) (assert (= c (+ a b)))
        ;;@ (spec (sig (args a, b) (r))
        ;;@     (assertions (= (+ (a) (b)) (r))))
        (decl iadd (Value Value) Inst)
        (extern extractor iadd iadd)
        
        ;;@ (spec (sig (args imm_arg) (ret))
        ;;@     (assertions (= (-(conv_from 12 (imm_arg))) (ret))))
        (decl imm12_from_negated_value (Imm12) Value)
        (extern extractor imm12_from_negated_value imm12_from_negated_value)
    ";
    let annotation_env = parse_annotations_str(code);

    assert_eq!(annotation_env.annotation_map.len(), 3);
    for (term, annotation) in annotation_env.annotation_map {
        let expected = isle_annotation_for_term(&term).unwrap();
        assert_eq!(expected, annotation);
    }
}
