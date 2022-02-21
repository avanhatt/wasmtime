pub mod parser;

#[test]
fn parser() {
    assert!(parser::TypeParser::new().parse("bool").is_ok());
    assert!(parser::TypeParser::new().parse("bv8").is_ok());
}

fn main() {
    println!("Running tests..."); 
}
