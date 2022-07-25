use std::collections::{HashMap, HashSet};
use std::path::PathBuf;

use cranelift_isle as isle;
use veri_annotation::parser_wrapper::{parse_annotations, AnnotationEnv};
use veri_ir::annotation_ir;

fn main() {
	let files = vec!["files/iadd.isle"];
	let lexer = isle::lexer::Lexer::from_files(&files).unwrap();
    let path_buf = PathBuf::from(&files[0]);
    let annotation_env = parse_annotations(&vec![path_buf]);

    for (term, annotation) in annotation_env.annotation_map {
        println!("{}", term);
        let mut vars = HashSet::from([&annotation.sig.ret.name]);
        for arg in &annotation.sig.args {
            let _ = &vars.insert(&arg.name);
        }
        let mut init = HashMap::new();
        for assertion in &annotation.assertions {
            get_initial_types(assertion, &vars, String::from(""), &mut init);
        }
        println!("{:#?}", init);

        let mut result = vec![];
        for arg in annotation.sig.args {
            result.push(init[&arg.name].clone());
        }
        result.push(init[&annotation.sig.ret.name].clone());
        println!("{:#?}", result);
    }

	/*let defs = isle::parser::parse(lexer).expect("should parse");
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
	}*/
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

// TODO: what if multiple assertions affect each others' initally assigned types?
// as in fits_in_64
fn get_initial_types(
    expr: &Box<annotation_ir::Expr>,
    vars: &HashSet<&String>,
    curr_type: String,
    initial_types: &mut HashMap<String, String>,
) -> String {
    match &**expr {
        annotation_ir::Expr::Var(name) => {
            // TODO: currently a hacky way to deal with fits_in_64 (see above)
            // if we already have a non-polymorphic type from some other assertion
            // do not overwrite it
            // another option is that we can type each assertion independently
            // and choose the most specific type at the end
            // but assertions may not be independent :(
            if initial_types.contains_key(name) && initial_types[name] != "t" {
                return initial_types[name].clone();
            }

            // original logic when I wasn't worried about multiple assertions
            if vars.contains(name) {
                let _ = &initial_types.insert(name.to_string(), curr_type.clone());
            }
            curr_type
        }
        annotation_ir::Expr::Const(c) => {
            c.ty.to_string()
        }
        annotation_ir::Expr::TyWidth => {
            String::from("Int")
        }
        annotation_ir::Expr::Eq(x, y) => {
            // TODO: make this less sketchy
            let t1 = get_initial_types(&x, &vars, String::from("t"), initial_types);
            let t2 = get_initial_types(&y, &vars, String::from("t"), initial_types);
            if &t1 != "t" && &t2 == "t" {
                get_initial_types(&y, &vars, t1.clone(), initial_types);
            }
            if &t1 == "t" && t2 != "t" {
                get_initial_types(&x, &vars, t2.clone(), initial_types);
            }
            String::from("bool")
        }
        annotation_ir::Expr::BVAdd(x, y) => {
            get_initial_types(&x, &vars, String::from("bv"), initial_types);
            get_initial_types(&y, &vars, String::from("bv"), initial_types);
            String::from("bv")
        }
        annotation_ir::Expr::Lte(x, y) => {
            // TODO: make this less sketchy
            let t1 = get_initial_types(&x, &vars, String::from("t"), initial_types);
            let t2 = get_initial_types(&y, &vars, String::from("t"), initial_types);
            if &t1 != "t" && &t2 == "t" {
                get_initial_types(&y, &vars, t1.clone(), initial_types);
            }
            if &t1 == "t" && t2 != "t" {
                get_initial_types(&x, &vars, t2.clone(), initial_types);
            }
            String::from("bool")
        }
        _ => todo!()
    }
}