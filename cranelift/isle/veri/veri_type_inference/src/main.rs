use std::collections::{HashMap, HashSet};
use std::path::PathBuf;

use cranelift_isle as isle;
use veri_annotation::parser_wrapper::{parse_annotations, AnnotationEnv};

fn main() {
	let files = vec!["files/uextend.isle"];
	let lexer = isle::lexer::Lexer::from_files(&files).unwrap();
    let path_buf = PathBuf::from(&files[0]);
    let annotation_env = parse_annotations(&vec![path_buf]);

	let defs = isle::parser::parse(lexer).expect("should parse");
    // TODO: clean up
    let mut parse_tree = RuleParseTree {
        lhs: ParseTreeNode{
            ident: "".to_string(),
            type_var: 0,
            children: vec![],
        },
        rhs: ParseTreeNode{
            ident: "".to_string(),
            type_var: 0,
            children: vec![],
        },
        type_var_map: HashMap::new(),
        next_type_var: 1
    };
	for def in defs.defs {
        parse_tree = match def {
            isle::ast::Def::Rule(r) => create_parse_tree(r),
            _ => continue,
        };
        println!("{:#?}", parse_tree);
	}

    let mut constraints = HashSet::new();
    generate_constraints_help(annotation_env, &parse_tree, &parse_tree.lhs, constraints);
}

#[derive(Debug)]
struct RuleParseTree {
    lhs: ParseTreeNode,
    rhs: ParseTreeNode,
    type_var_map: HashMap<String, u32>,
    next_type_var: u32,
}

#[derive(Debug)]
struct ParseTreeNode {
    ident: String,
    type_var: u32,
    children: Vec<ParseTreeNode>,
}

fn create_parse_tree(rule: isle::ast::Rule) -> RuleParseTree {
    // TODO: clean up
    let mut tree = RuleParseTree{
        lhs: ParseTreeNode{
            ident: "".to_string(),
            type_var: 0,
            children: vec![],
        },
        rhs: ParseTreeNode{
            ident: "".to_string(),
            type_var: 0,
            children: vec![],
        },
        type_var_map: HashMap::new(),
        next_type_var: 1
    };

    let lhs = create_parse_tree_pattern(rule.pattern, &mut tree);
    let rhs = create_parse_tree_expr(rule.expr, &mut tree);

    tree.lhs = lhs;
    tree.rhs = rhs;
    tree
}

fn create_parse_tree_pattern(
    pattern: isle::ast::Pattern,
    tree: &mut RuleParseTree,
) -> ParseTreeNode {
    match pattern {
        isle::ast::Pattern::Term{ sym, args, .. } => {
            // process children first
            let mut children = vec![];
            for arg in args {
                let child = create_parse_tree_pattern(arg, tree);
                children.push(child);
            }

            // if we've already typed this term use the same type
            // otherwise use a fresh type and increment the global counter
            let ident = sym.0;
            tree.type_var_map.entry(ident.clone()).or_insert(tree.next_type_var);
            let type_var = tree.type_var_map[&ident];
            if type_var == tree.next_type_var {
                tree.next_type_var += 1;
            }

            ParseTreeNode{
                ident: ident.clone(),
                type_var: type_var,
                children: children,
            }
        }
        isle::ast::Pattern::Var{ var, .. } => {
            let ident = var.0;
            
            tree.type_var_map.entry(ident.clone()).or_insert(tree.next_type_var);
            let type_var = tree.type_var_map[&ident];
            if type_var == tree.next_type_var {
                tree.next_type_var += 1;
            }
           
            // this is a base case so there are no children
            ParseTreeNode{
                ident: ident.clone(),
                type_var: type_var,
                children: vec![],
            }
        }
        _ => todo!()
    }
}

fn create_parse_tree_expr(
    expr: isle::ast::Expr,
    tree: &mut RuleParseTree,
) -> ParseTreeNode {
    match expr {
        isle::ast::Expr::Term{ sym, args, .. } => {
            let mut children = vec![];
            for arg in args {
                let child = create_parse_tree_expr(arg, tree);
                children.push(child);
            }

            let ident = sym.0;
            tree.type_var_map.entry(ident.clone()).or_insert(tree.next_type_var);
            let type_var = tree.type_var_map[&ident];
            if type_var == tree.next_type_var {
                tree.next_type_var += 1;
            }

            ParseTreeNode{
                ident: ident.clone(),
                type_var: type_var,
                children: children,
            }
        }
        isle::ast::Expr::Var{ name, .. } => {
            let ident = name.0;
            
            tree.type_var_map.entry(ident.clone()).or_insert(tree.next_type_var);
            let type_var = tree.type_var_map[&ident];
            if type_var == tree.next_type_var {
                tree.next_type_var += 1;
            }
           
            ParseTreeNode{
                ident: ident.clone(),
                type_var: type_var,
                children: vec![],
            }
        }
        // bind pattern case: assign same type var to bound var and top level subpat because we lose that info in our parse tree
        _ => todo!()
    }
}

fn generate_constraints_help(
    annotations: AnnotationEnv,
    tree: &RuleParseTree,
    curr: &ParseTreeNode,
    constraints: HashSet<(u32, u32)>,
) {
    let name = &curr.ident;
    let a = annotations.get_annotation_for_term(&name);
    match a {
        None => return,
        Some(annotation) => {

        }
    };

    // ;;1. traverse over rule (see lower is the first term)
    // ;;2. get lower's annotation
    // ;;3. check assertions, ie = arg ret
    // ;;4. see that arg = sig.args[0] so it's lower.children[0]
    // ;;5. see that ret is the ret so it's lower.children[-1]
    // ;;6. since assertion is equality set type vars equal
    // ;;7. somehow mark that we want arg and ret's types???    

    // ;;8. for has_type, tywidth has known type: Int    

    // ;;9. for fits_in_64, 64 is an Int const    

    // ;;10. for iadd, x and y have same (bv or Int) type
    // ;;11. ret has the same type too    

    // ;;12. add constraint for LHS = RHS??
}