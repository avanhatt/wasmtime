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

    for (term, annotation) in &annotation_env.annotation_map {
        let types = get_initial_types(term, &annotation_env);
        println!("{}: {:#?}", term, types);
    }

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

    // TODO: add rhs
    let mut constraints = HashSet::new();
    generate_constraints(&annotation_env, &parse_tree, &parse_tree.lhs, &mut constraints);
    println!("{:#?}", constraints);
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

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Type {
    Poly(u32),
    Known(annotation_ir::Type),
}

// TODO: what if multiple assertions affect each others' initally assigned types?
// as in fits_in_64
// TODO: fix polymorphism (don't hardcode Poly(0) everywhere)
fn get_initial_types_help(
    expr: &Box<annotation_ir::Expr>,
    vars: &HashSet<&String>,
    curr_type: Type,
    initial_types: &mut HashMap<String, Type>,
) -> Type {
    match &**expr {
        annotation_ir::Expr::Var(name) => {
            // TODO: currently a hacky way to deal with fits_in_64 (see above)
            // if we already have a non-polymorphic type from some other assertion
            // do not overwrite it
            // another option is that we can type each assertion independently
            // and choose the most specific type at the end
            // but assertions may not be independent :(
            if initial_types.contains_key(name) && initial_types[name] != Type::Poly(0) {
                return initial_types[name].clone();
            }

            // Original logic when I wasn't worried about multiple assertions.
            // On the way down, start with a general type and get more specific as
            // we encouter operators that enforce more strict type requirements.
            if vars.contains(name) {
                let _ = &initial_types.insert(name.to_string(), curr_type.clone());
            }
            curr_type
        }
        annotation_ir::Expr::Const(c) => {
            Type::Known(c.ty.clone())
        }
        annotation_ir::Expr::TyWidth => {
            Type::Known(annotation_ir::Type::Int)
        }
        annotation_ir::Expr::Eq(x, y) => {
            // TODO: make this less sketchy
            let t1 = get_initial_types_help(&x, &vars, Type::Poly(0), initial_types);
            let t2 = get_initial_types_help(&y, &vars, Type::Poly(0), initial_types);
            // On the way back up, if we have recovered a more specific type from going down,
            // try going back down with this more specific initial type.
            // If no specific type could be recovered, leave both subtrees polymorphic.
            if t1 != Type::Poly(0) && t2 == Type::Poly(0) {
                get_initial_types_help(&y, &vars, t1.clone(), initial_types);
            }
            if t1 == Type::Poly(0) && t2 != Type::Poly(0) {
                get_initial_types_help(&x, &vars, t2.clone(), initial_types);
            }
            Type::Known(annotation_ir::Type::Bool)
        }
        annotation_ir::Expr::BVAdd(x, y) => {
            get_initial_types_help(
                &x, 
                &vars, 
                Type::Known(annotation_ir::Type::BitVector), 
                initial_types,
            );
            get_initial_types_help(
                &y, 
                &vars, 
                Type::Known(annotation_ir::Type::BitVector), 
                initial_types,
            );
            Type::Known(annotation_ir::Type::BitVector)
        }
        annotation_ir::Expr::Lte(x, y) => {
            // TODO: make this less sketchy
            let t1 = get_initial_types_help(&x, &vars, Type::Poly(0), initial_types);
            let t2 = get_initial_types_help(&y, &vars, Type::Poly(0), initial_types);
            if t1 != Type::Poly(0) && t2 == Type::Poly(0) {
                get_initial_types_help(&y, &vars, t1.clone(), initial_types);
            }
            if t1 == Type::Poly(0) && t2 != Type::Poly(0) {
                get_initial_types_help(&x, &vars, t2.clone(), initial_types);
            }
            Type::Known(annotation_ir::Type::Bool)
        }
        _ => todo!()
    }
}

fn get_initial_types(term: &str, annotation_env: &AnnotationEnv) -> Vec<Type> {
    let annotation = annotation_env.get_annotation_for_term(&term).unwrap();

    let mut vars = HashSet::from([&annotation.sig.ret.name]);
    for arg in &annotation.sig.args {
        let _ = &vars.insert(&arg.name);
    }

    let mut init = HashMap::new();

    for assertion in &annotation.assertions {
        get_initial_types_help(assertion, &vars, Type::Poly(0), &mut init);
    }
    
    // for easy mapping to rule parse trees
    let mut result = vec![];
    for arg in annotation.sig.args {
        result.push(init[&arg.name].clone());
    }
    result.push(init[&annotation.sig.ret.name].clone());
    result
}

#[derive(Debug, Eq, Hash, PartialEq)]
pub enum TypeVar {
    Known(crate::Type),
    Var(u32),
}

fn generate_constraints(
    annotations: &AnnotationEnv,
    tree: &RuleParseTree,
    curr: &ParseTreeNode,
    constraints: &mut HashSet<(u32, TypeVar)>,
) {
    if curr.children.len() == 0 {
        return;
    }

    let name = &curr.ident;
    let a = annotations.get_annotation_for_term(&name);
    let initial_types = get_initial_types(&name, &annotations);

    // TODO: make this not burn the eyes
    let ret_index = initial_types.len() - 1;
    for (i, var) in initial_types.iter().enumerate() {
        match var {
            // If we know the type of some var from the annotation, set it.
            Type::Known(ref t) => {
                if i == ret_index {
                    constraints.insert((curr.type_var, TypeVar::Known(var.clone())));
                } else {
                    constraints.insert((curr.children[i].type_var, TypeVar::Known(var.clone())));
                }
            }
            // If not, at least we know "relative polymorphic types."
            // If there's some other var with the same polymorphic type,
            // add a constraint that they must be equal.
            Type::Poly(n) => {
                // if ret is polymorphic and there is some other var that has
                // the same type we will already have that constraint by this point
                if i == ret_index {
                    continue;
                }

                for(j, var2) in initial_types.iter().enumerate() {
                    if i == j {
                        continue;
                    }
                    if var == var2 {
                        if j == ret_index {
                            constraints.insert(
                                (curr.children[i].type_var, TypeVar::Var(curr.type_var))
                            );
                        } else {
                            constraints.insert(
                                (
                                    curr.children[i].type_var, 
                                    TypeVar::Var(curr.children[j].type_var),
                                )
                            );
                        }
                    }
                }
            }
        }
    }

    for child in &curr.children {
        generate_constraints(&annotations, tree, &child, constraints);
    }
}