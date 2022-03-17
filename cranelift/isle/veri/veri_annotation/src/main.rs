pub mod parser;

#[test]
fn parser() {
    // types
    assert!(parser::VIRTypeParser::new().parse("bv8").is_ok());
    assert!(parser::VIRTypeParser::new().parse("bvlist(4, 8)").is_ok());
    assert!(parser::VIRTypeParser::new().parse("func(bv8, bv8) IsleType").is_ok());
    assert!(parser::VIRTypeParser::new().parse("bool").is_ok());
    assert!(parser::VIRTypeParser::new().parse("IsleType").is_ok());

    // bound var
    assert!(parser::BoundVarParser::new().parse("b: bv16").is_ok());
    assert!(parser::BoundVarParser::new().parse("bv: bv32").is_err());
    assert!(parser::BoundVarParser::new().parse("ty: bvlist(1, 10)").is_ok());
    assert!(parser::BoundVarParser::new().parse("foo: func(bool, bool) bv8").is_ok());
    assert!(parser::BoundVarParser::new().parse("arg: bool").is_ok());
    assert!(parser::BoundVarParser::new().parse("ba: IsleType").is_ok());

    // function annotation
    assert!(parser::FunctionAnnotationParser::new()
        .parse("(sig (args) (ret: bool))").is_ok());
    assert!(parser::FunctionAnnotationParser::new()
        .parse("(sig (args a: bool) (ret: bool))").is_ok());
    assert!(parser::FunctionAnnotationParser::new()
        .parse("(sig (args a: bool, b: bv16) (ret: bool))").is_ok());

    // vir expr
    assert!(parser::VIRExprParser::new().parse("10i16").is_ok());
    assert!(parser::VIRExprParser::new().parse("-10i8").is_ok());
    assert!(parser::VIRExprParser::new().parse("(b: bv16)").is_ok());
    assert!(parser::VIRExprParser::new().parse("(True)").is_ok());
    assert!(parser::VIRExprParser::new().parse("(False)").is_ok());
    //TODO: test things like !a, a && b, ~b, etc.

    /*
    let r = parser::BoundVarParser::new().parse("ty: bvlist(1, 10)");
    match r {
        Ok(_) => println!("woohoo!"),
        Err(err) => panic!("{:?}", err),
    };
    */

    // TODO: add assertions, compare fields in real annotations
}

fn main() {
    println!("Running tests..."); 
}
