use pest::Parser;
use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "ast.pest"]
struct ASTParser;

pub fn parse(src: &str) {
    ASTParser::parse(Rule::nodes, src).unwrap();
}
