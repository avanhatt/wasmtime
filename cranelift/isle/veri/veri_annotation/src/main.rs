pub mod parser;

#[test]
fn parser() {
    // types
    assert!(parser::VIRTypeParser::new().parse("bool").is_ok());
    assert!(parser::VIRTypeParser::new().parse("bv8").is_ok());
    assert!(parser::VIRTypeParser::new().parse("IsleType").is_ok());

    // bound var
    assert!(parser::BoundVarParser::new().parse("b: bv16").is_ok());
    assert!(parser::BoundVarParser::new().parse("arg: bool").is_ok());
    assert!(parser::BoundVarParser::new().parse("ba: IsleType").is_ok());
    assert!(parser::BoundVarParser::new().parse("bv: bv32").is_err());

    // function annotation
    assert!(parser::FunctionAnnotationParser::new()
        .parse("(sig (args) (ret: bool))").is_ok());
    assert!(parser::FunctionAnnotationParser::new()
        .parse("(sig (args a: bool) (ret: bool))").is_ok());
    assert!(parser::FunctionAnnotationParser::new()
        .parse("(sig (args a: bool, b: bv16) (ret: bool))").is_ok());

    // bool expr
    assert!(parser::BoolExprParser::new().parse("(True)").is_ok());
    assert!(parser::BoolExprParser::new().parse("(False)").is_ok());
    assert!(parser::BoolExprParser::new().parse("(Not (False))").is_ok());

    /*
    let r = parser::FunctionAnnotationParser::new().parse("(sig (args a: bool, b: bv16) (ret: bool))");
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
