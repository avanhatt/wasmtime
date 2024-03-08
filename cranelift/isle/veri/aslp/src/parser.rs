use crate::raw::{Array, Block, Func, Node, Term};
use enquote::unquote;
use pest::{
    iterators::{Pair, Pairs},
    Parser,
};
use pest_derive::Parser;
use tracing::debug;

#[derive(Parser)]
#[grammar = "raw.pest"]
struct RawParser;

pub fn parse(src: &str) -> anyhow::Result<Block> {
    let pairs = RawParser::parse(Rule::nodes, src)?;
    parse_block(pairs)
}

fn parse_block(pairs: Pairs<Rule>) -> anyhow::Result<Block> {
    let nodes = parse_nodes(pairs)?;
    Ok(Block { nodes })
}

fn parse_nodes(pairs: Pairs<Rule>) -> anyhow::Result<Vec<Box<Node>>> {
    let mut nodes = Vec::new();
    for pair in pairs {
        let rule = pair.as_rule();
        debug!(?rule, "parse nodes");
        match rule {
            Rule::node => nodes.push(Box::new(parse_node(pair)?)),
            Rule::EOI => break,
            _ => unreachable!("non-node in nodes list: {}", pair),
        }
    }
    Ok(nodes)
}

fn parse_node(pair: Pair<Rule>) -> anyhow::Result<Node> {
    let rule = pair.as_rule();
    debug!(?rule, "parse node");
    match rule {
        Rule::node => parse_node(pair.into_inner().next().unwrap()),
        Rule::term => {
            let mut pair = pair.into_inner();
            let ident = pair.next().unwrap();
            let arg_list = pair.next().unwrap();
            let args = parse_nodes(arg_list.into_inner())?;
            Ok(Node::Term(Term {
                name: ident.as_str().to_string(),
                args,
            }))
        }
        Rule::array => {
            let elements = parse_nodes(pair.into_inner())?;
            Ok(Node::Array(Array { elements }))
        }
        Rule::block => {
            let block = parse_block(pair.into_inner())?;
            Ok(Node::Block(block))
        }
        Rule::func_ident => {
            let mut pair = pair.into_inner();
            let ident = pair.next().unwrap();
            let id = pair.next().unwrap();
            Ok(Node::Func(Func {
                name: ident.as_str().to_string(),
                id: id.as_str().parse()?,
            }))
        }
        Rule::ident => Ok(Node::Var(pair.as_str().to_string())),
        Rule::string => Ok(Node::String(unquote(pair.as_str())?)),
        _ => unreachable!("unexpected node type: {}", pair),
    }
}
