use veri_ir::isle_annotations::{isle_annotation_for_term};
use veri_annotation::parser_wrapper::{parse};

#[test]
fn test_parser() {
    let annotation_env = parse("examples/simple.isle");
    assert_eq!(annotation_env.annotation_map.len(), 9);
    for (term, annotation) in annotation_env.annotation_map {
        let expected = isle_annotation_for_term(&term).unwrap();
        assert_eq!(expected, annotation);
    }
}
