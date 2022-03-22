use veri_ir::annotation_ir::*;
use veri_engine::isle_annotations::{isle_annotation_for_term};

pub mod parser;

#[test]
fn parser() {
    // type
    assert!(parser::TypeParser::new().parse("bv").is_ok());
    assert!(parser::TypeParser::new().parse("bvlist(16)").is_ok());
    assert!(parser::TypeParser::new().parse("(func(bv) (isleType))").is_ok());
    assert!(parser::TypeParser::new().parse("bool").is_ok());
    assert!(parser::TypeParser::new().parse("isleType").is_ok());
    
    // bound var
    assert!(parser::BoundVarParser::new().parse("b").is_ok());
    assert!(parser::BoundVarParser::new().parse("bv").is_err());
    assert!(parser::BoundVarParser::new().parse("ty: bvlist(1)").is_ok());
    assert!(parser::BoundVarParser::new().parse("foo: (func(bool, bool) (bv))").is_ok());
    assert!(parser::BoundVarParser::new().parse("arg").is_ok());
    assert!(parser::BoundVarParser::new().parse("ba").is_ok());
    
    // term signature
    assert!(parser::TermSignatureParser::new()
        .parse("(sig (args) (ret: bool))").is_ok());
    assert!(parser::TermSignatureParser::new()
        .parse("(sig (args a: bool) (ret: bool))").is_ok());
    assert!(parser::TermSignatureParser::new()
        .parse("(sig (args a: bool, b: bv) (ret: bool))").is_ok());

    // function type
    assert!(parser::FunctionTypeParser::new()
        .parse("func(bool, bv) (isleType)").is_ok());
    assert!(parser::FunctionTypeParser::new().parse("func() (bv)").is_ok());
    assert!(parser::FunctionTypeParser::new()
        .parse("func((func(isleType, bv) (bool))) (isleType)").is_ok());
    assert!(parser::FunctionTypeParser::new().parse("func() ()").is_err());

    // function
    assert!(parser::FunctionParser::new().parse(
        "foo(a, b) (bv) {(+ (var a) (var b))}").is_ok());
    assert!(parser::FunctionParser::new().parse(
        "xor(a, b) (bool) {
            (|| (&& (!(var a)) (var b)) (&& (var a) (!(var b))))
        }").is_ok());

    // function application
    assert!(parser::FunctionApplicationParser::new()
        .parse("(var foo)((var a), (var b))").is_ok());

    // const
    assert!(parser::ConstParser::new().parse("10i: bv").is_ok());
    assert!(parser::ConstParser::new().parse("true: bool").is_err());
    
    // vir expr: consts
    assert!(parser::ExprParser::new().parse("(var a)").is_ok());
    assert!(parser::ExprParser::new().parse("(-1i: bv)").is_ok());
    assert!(parser::ExprParser::new().parse("(true)").is_ok());
    assert!(parser::ExprParser::new().parse("(false)").is_ok());
    assert!(parser::ExprParser::new().parse("(tywidth)").is_ok());
    // vir expr: boolean operations
    assert!(parser::ExprParser::new().parse("(!(var a))").is_ok());
    assert!(parser::ExprParser::new().parse("(&& (var a) (var b))").is_ok());
    assert!(parser::ExprParser::new().parse("(|| (var a) (false))").is_ok());
    assert!(parser::ExprParser::new().parse("(=> (true) (var b))").is_ok());
    assert!(parser::ExprParser::new().parse("(= (var a) (false))").is_ok());
    assert!(parser::ExprParser::new().parse("(<= (var a) (10i: bv))").is_ok());
    assert!(parser::ExprParser::new()
        .parse("(&& (|| (var a) (var b)) (var c))").is_ok());
    assert!(parser::ExprParser::new().parse("(&& (!(var a)) (var b))").is_ok());
    // vir expr: bv operations
    assert!(parser::ExprParser::new().parse("(-(var a))").is_ok());
    assert!(parser::ExprParser::new().parse("(~(var a))").is_ok());
    assert!(parser::ExprParser::new().parse("(+ (-(var a)) (var b))").is_ok());
    assert!(parser::ExprParser::new().parse("(- (var a) (~(var b)))").is_ok());
    assert!(parser::ExprParser::new().parse("(& (var a) (var b))").is_ok());
    // vir expr: conversions
    assert!(parser::ExprParser::new().parse("(zero_ext 4 (var a))").is_ok());
    assert!(parser::ExprParser::new().parse("(siin_ext 2 (-12i: bv))").is_ok());
    assert!(parser::ExprParser::new().parse("(extract 0 8 (var a))").is_ok());
    assert!(parser::ExprParser::new().parse("(conv_to 6 (var b))").is_ok());
    assert!(parser::ExprParser::new().parse("(conv_from 16 (8i: bv))").is_ok());
    // vir expr: functions
    assert!(parser::ExprParser::new()
        .parse("(f(x) (bv) {(+ (var x) (1i:bv))})").is_ok());
    assert!(parser::ExprParser::new()
        .parse("((var f)((2i:bv)))").is_ok());
    assert!(parser::ExprParser::new()
        .parse("((var a),(true),(3i: bv))").is_ok());
    assert!(parser::ExprParser::new()
        .parse("(get (var x) 0)").is_ok());

    // term annotation
    assert!(parser::TermAnnotationParser::new()
        .parse("(spec (sig (args x, y) (ret))
            (assertions (= (+ (var x) (var y)) (var ret))))").is_ok());

    // "lower" | "put_in_reg" | "value_reg" | "first_result" | "inst_data"
    let parsed = parser::TermAnnotationParser::new().parse(
        "(spec (sig (args arg) (ret))
            (assertions (= (var arg) (var ret))))"
    ).unwrap();

    let expected = isle_annotation_for_term("lower").unwrap();
    assert!(expected, parsed);

    /*let arg = BoundVar{name: "arg".to_string(), ty: None};
    let ret = BoundVar{name: "ret".to_string(), ty: None};
    let v1 = Box::new(Expr::Var(arg.name.clone()));
    let v2 = Box::new(Expr::Var(ret.name.clone()));
    let a1 = Box::new(Expr::Eq(v1, v2));

    assert!(r.sig.args == vec![arg]);
    assert!(r.sig.ret == ret);
    assert!(r.assertions == vec![a1]);
    */
    // "InstructionData.Binary"
    let r = parser::TermAnnotationParser::new().parse(
        "(spec (sig (args opcode: (func(bvlist(2)) (bv)), arg_list) (ret))
            (assertions (= (((var opcode)((var arg_list)))) (var ret))))"
    ).unwrap();
}

fn main() {
    println!("Running tests..."); 
}
