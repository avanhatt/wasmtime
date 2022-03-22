use veri_ir::isle_annotations::isle_annotation_for_term;

pub mod parser;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_type() {
        assert!(parser::TypeParser::new().parse("bv").is_ok());
        assert!(parser::TypeParser::new().parse("bvlist(16)").is_ok());
        assert!(parser::TypeParser::new().parse("(func(bv) (isleType))").is_ok());
        assert!(parser::TypeParser::new().parse("bool").is_ok());
        assert!(parser::TypeParser::new().parse("isleType").is_ok());
    }

    #[test]
    fn test_bound_var() {
        assert!(parser::BoundVarParser::new().parse("b").is_ok());
        assert!(parser::BoundVarParser::new().parse("bv").is_err());
        assert!(parser::BoundVarParser::new().parse("ty: bvlist(1)").is_ok());
        assert!(parser::BoundVarParser::new().parse(
            "foo: (func(bool, bool) (bv))").is_ok());
        assert!(parser::BoundVarParser::new().parse("arg").is_ok());
        assert!(parser::BoundVarParser::new().parse("ba").is_ok());
    }

    #[test]
    fn test_term_signature() {    
        assert!(parser::TermSignatureParser::new()
            .parse("(sig (args) (ret: bool))").is_ok());
        assert!(parser::TermSignatureParser::new()
            .parse("(sig (args a: bool) (ret: bool))").is_ok());
        assert!(parser::TermSignatureParser::new()
            .parse("(sig (args a: bool, b: bv) (ret: bool))").is_ok());
    }
    
    #[test]
    fn test_function_type() {
        assert!(parser::FunctionTypeParser::new()
            .parse("func(bool, bv) (isleType)").is_ok());
        assert!(parser::FunctionTypeParser::new().parse("func() (bv)").is_ok());
        assert!(parser::FunctionTypeParser::new()
            .parse("func((func(isleType, bv) (bool))) (isleType)").is_ok());
        assert!(parser::FunctionTypeParser::new().parse("func() ()").is_err());
    }

    #[test]
    fn test_function() {
        assert!(parser::FunctionParser::new().parse(
            "Opcode.Iadd(a, b) (bv) {(+ (var a) (var b))}").is_ok());
        assert!(parser::FunctionParser::new().parse(
            "xor(a, b) (bool) {
                (|| (&& (!(var a)) (var b)) (&& (var a) (!(var b))))
            }").is_ok());
    }    

    #[test]
    fn test_function_application() {
        assert!(parser::FunctionApplicationParser::new()
            .parse("(var foo)((var a), (var b))").is_ok());
    }

    #[test]
    fn test_const() {
        assert!(parser::ConstParser::new().parse("10i: bv").is_ok());
        assert!(parser::ConstParser::new().parse("true: bool").is_err());
    }

    #[test]
    fn test_expr() {
        // consts
        assert!(parser::ExprParser::new().parse("(var a)").is_ok());
        assert!(parser::ExprParser::new().parse("(-1i: bv)").is_ok());
        assert!(parser::ExprParser::new().parse("(true)").is_ok());
        assert!(parser::ExprParser::new().parse("(false)").is_ok());
        assert!(parser::ExprParser::new().parse("(tywidth)").is_ok());

        // boolean operations
        assert!(parser::ExprParser::new().parse("(!(var a))").is_ok());
        assert!(parser::ExprParser::new().parse("(&& (var a) (var b))").is_ok());
        assert!(parser::ExprParser::new().parse("(|| (var a) (false))").is_ok());
        assert!(parser::ExprParser::new().parse("(=> (true) (var b))").is_ok());
        assert!(parser::ExprParser::new().parse("(= (var a) (false))").is_ok());
        assert!(parser::ExprParser::new().parse("(<= (var a) (10i: bv))").is_ok());
        assert!(parser::ExprParser::new()
            .parse("(&& (|| (var a) (var b)) (var c))").is_ok());
        assert!(parser::ExprParser::new().parse("(&& (!(var a)) (var b))").is_ok());

        // bv operations
        assert!(parser::ExprParser::new().parse("(-(var a))").is_ok());
        assert!(parser::ExprParser::new().parse("(~(var a))").is_ok());
        assert!(parser::ExprParser::new().parse("(+ (-(var a)) (var b))").is_ok());
        assert!(parser::ExprParser::new().parse("(- (var a) (~(var b)))").is_ok());
        assert!(parser::ExprParser::new().parse("(& (var a) (var b))").is_ok());

        // conversions
        assert!(parser::ExprParser::new().parse("(zero_ext 4 (var a))").is_ok());
        assert!(parser::ExprParser::new().parse("(siin_ext 2 (-12i: bv))").is_ok());
        assert!(parser::ExprParser::new().parse("(extract 0 8 (var a))").is_ok());
        assert!(parser::ExprParser::new().parse("(conv_to 6 (var b))").is_ok());
        assert!(parser::ExprParser::new().parse("(conv_from 16 (8i: bv))").is_ok());

        // functions
        assert!(parser::ExprParser::new()
            .parse("(f(x) (bv) {(+ (var x) (1i:bv))})").is_ok());
        assert!(parser::ExprParser::new()
            .parse("((var f)((2i:bv)))").is_ok());
        assert!(parser::ExprParser::new()
            .parse("((var a),(true),(3i: bv))").is_ok());
        assert!(parser::ExprParser::new()
            .parse("(get (var x) 0)").is_ok());
    }

    #[test]
    fn test_term_annotation() {
        assert!(parser::TermAnnotationParser::new()
            .parse("(spec (sig (args x, y) (ret))
                (assertions (= (+ (var x) (var y)) (var ret))))").is_ok());
    }

    #[test]
    fn test_real_annotations() {
        // "lower" | "put_in_reg" | "value_reg" | "first_result" | "inst_data"
        let parsed = parser::TermAnnotationParser::new().parse(
            "(spec (sig (args arg) (ret))
                (assertions (= (var arg) (var ret))))"
        ).unwrap();
        let expected = isle_annotation_for_term("lower").unwrap();
        assert_eq!(parsed, expected);
    
        // InstructionData.Binary
        let parsed = parser::TermAnnotationParser::new().parse(
            "(spec (sig (args opcode: (func(bvlist(2)) (bv)), arg_list) (ret))
                (assertions (= ((var opcode)((var arg_list))) (var ret))))"
        ).unwrap();
        let expected = isle_annotation_for_term("InstructionData.Binary").unwrap();
        assert_eq!(parsed, expected);
    
        // value_type
        let parsed = parser::TermAnnotationParser::new().parse(
            "(spec (sig (args arg) (ret))
                (assertions (= (var arg) (tywidth))))"
        ).unwrap();
        let expected = isle_annotation_for_term("value_type").unwrap();
        assert_eq!(parsed, expected);
    
        // value_array_2
        let parsed = parser::TermAnnotationParser::new().parse(
            "(spec (sig (args arg1, arg2) (ret))
                (assertions (= ((var arg1), (var arg2)) (var ret))))"
        ).unwrap();
        let expected = isle_annotation_for_term("value_array_2").unwrap();
        assert_eq!(parsed, expected);
    
        // has_type
        let parsed = parser::TermAnnotationParser::new().parse(
            "(spec (sig (args ty, arg) (ret))
                (assertions (= (var ty) (tywidth)), (= (var arg) (var ret))))"
        ).unwrap();
        let expected = isle_annotation_for_term("has_type").unwrap();
        assert_eq!(parsed, expected);
    
        // fits_in_64
        let parsed = parser::TermAnnotationParser::new().parse(
            "(spec (sig (args arg) (ret))
                (assertions (= (var arg) (var ret)), (<= (var arg) (64i: isleType))))"
        ).unwrap();
        let expected = isle_annotation_for_term("fits_in_64").unwrap();
        assert_eq!(parsed, expected);
        
        // iadd
        let parsed = parser::TermAnnotationParser::new().parse(
            "(spec (sig (args a, b) (r))
                (assertions (= (+ (var a) (var b)) (var r))))"
        ).unwrap();
        let expected = isle_annotation_for_term("iadd").unwrap();
        assert_eq!(parsed, expected);
    
        // Opcode.Iadd
        let parsed = parser::TermAnnotationParser::new().parse(
            "(spec (sig (args) (r))
                (assertions (= (var r) (Opcode.Iadd (xs) ((func (bvlist(2)) (bv))) {
                    (+ (get (var xs) 0) (get (var xs) 1))
                }))))"
        ).unwrap();
        let expected = isle_annotation_for_term("Opcode.Iadd").unwrap();
        assert_eq!(parsed, expected);
    
        // add
        let parsed = parser::TermAnnotationParser::new().parse(
            "(spec (sig (args ty, a, b) (r))
                (assertions (= (+ (var a) (var b)) (var r))))"
        ).unwrap();
        let expected = isle_annotation_for_term("add").unwrap();
        assert_eq!(parsed, expected);
    
        // imm12_from_negated_value
        let parsed = parser::TermAnnotationParser::new().parse(
            "(spec (sig (args imm_arg) (ret))
                (assertions (= (-(conv_from 12 (var imm_arg))) (var ret))))"
        ).unwrap();
        let expected = isle_annotation_for_term("imm12_from_negated_value")
            .unwrap();
        assert_eq!(parsed, expected);
    
        // sub_imm
        let parsed = parser::TermAnnotationParser::new().parse(
            "(spec (sig (args ty, reg, imm_arg) (ret))
                (assertions (= (-(var reg) (conv_from 12 (var imm_arg))) (var ret))))"
        ).unwrap();
        let expected = isle_annotation_for_term("sub_imm").unwrap();
        assert_eq!(parsed, expected);
    }
}

fn main() {
    println!("Running tests..."); 
}
