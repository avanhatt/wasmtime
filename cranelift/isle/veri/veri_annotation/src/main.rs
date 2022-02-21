#[macro_use] extern crate lalrpop_util;

lalrpop_mod!(pub parser);

#[test]
fn parser() {
    assert!(parser::TypeParser::new().parse("bool").is_ok());
}
