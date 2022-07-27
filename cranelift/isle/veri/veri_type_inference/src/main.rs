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

    for (term, _) in &annotation_env.annotation_map {
        let types = get_initial_types(term, &annotation_env);
        println!("{}: {:#?}", term, types);
    }

	let defs = isle::parser::parse(lexer).expect("should parse");
    // TODO: clean up
    let mut parse_tree = RuleParseTree {
        lhs: TypeVarNode{
            ident: "".to_string(),
            type_var: 0,
            children: vec![],
        },
        rhs: TypeVarNode{
            ident: "".to_string(),
            type_var: 0,
            children: vec![],
        },
        type_var_map: HashMap::new(),
        next_type_var: 1,
        term_to_type_var_map: HashMap::new(),
    };
	for def in defs.defs {
        parse_tree = match def {
            isle::ast::Def::Rule(r) => create_parse_tree(r),
            _ => continue,
        };
        println!("{:#?}", parse_tree);
	}

    let mut concrete_constraints = HashSet::new();
    let mut var_constraints = HashSet::new();
    generate_constraints(
        &annotation_env,
        &parse_tree,
        &parse_tree.lhs,
        &mut concrete_constraints,
        &mut var_constraints,
    );
    generate_constraints(
        &annotation_env,
        &parse_tree,
        &parse_tree.rhs,
        &mut concrete_constraints,
        &mut var_constraints,
    );
    println!("{:#?}", concrete_constraints);
    println!("{:#?}", var_constraints);

    let mut sub = HashMap::new();
    solve_constraints(
        &concrete_constraints,
        &var_constraints,
        &mut sub,
        (parse_tree.next_type_var - 1).try_into().unwrap(),
    );
    println!("{:#?}", sub);

    let results = type_annotations(&parse_tree, &sub);
    println!("{:#?}", results);
}

#[derive(Debug)]
struct RuleParseTree {
    lhs: TypeVarNode,
    rhs: TypeVarNode,
    type_var_map: HashMap<String, u32>,
    next_type_var: u32,
    term_to_type_var_map: HashMap<String, Vec<u32>>,
}

#[derive(Debug)]
struct TypeVarNode {
    ident: String,
    type_var: u32,
    children: Vec<TypeVarNode>,
}

fn create_parse_tree(rule: isle::ast::Rule) -> RuleParseTree {
    // TODO: clean up
    let mut tree = RuleParseTree{
        lhs: TypeVarNode{
            ident: "".to_string(),
            type_var: 0,
            children: vec![],
        },
        rhs: TypeVarNode{
            ident: "".to_string(),
            type_var: 0,
            children: vec![],
        },
        type_var_map: HashMap::new(),
        next_type_var: 1,
        term_to_type_var_map: HashMap::new(),
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
) -> TypeVarNode {
    match pattern {
        isle::ast::Pattern::Term{ sym, args, .. } => {
            // process children first
            let mut children = vec![];
            let mut type_vars = vec![];
            for arg in args {
                let child = create_parse_tree_pattern(arg, tree);
                type_vars.push(child.type_var);
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

            // even if we see the same term multiple times, the types should be the same
            type_vars.push(type_var);
            tree.term_to_type_var_map.insert(ident.clone(), type_vars);

            TypeVarNode{
                ident: ident,
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
            TypeVarNode{
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
) -> TypeVarNode {
    match expr {
        isle::ast::Expr::Term{ sym, args, .. } => {
            let mut children = vec![];
            let mut type_vars = vec![];
            for arg in args {
                let child = create_parse_tree_expr(arg, tree);
                type_vars.push(child.type_var);
                children.push(child);
            }

            let ident = sym.0;
            tree.type_var_map.entry(ident.clone()).or_insert(tree.next_type_var);
            let type_var = tree.type_var_map[&ident];
            if type_var == tree.next_type_var {
                tree.next_type_var += 1;
            }

            // even if we see the same term multiple times, the types should be the same
            type_vars.push(type_var);
            tree.term_to_type_var_map.insert(ident.clone(), type_vars);

            TypeVarNode{
                ident: ident,
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
           
            TypeVarNode{
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
        // TODO: DO NOT HARDCODE THIS CASE!! Hacky fix for terms like add
        if !init.contains_key(&arg.name) {
            init.insert(arg.name.clone(), Type::Known(annotation_ir::Type::Int));
        }
        result.push(init[&arg.name].clone());
    }
    result.push(init[&annotation.sig.ret.name].clone());
    result
}

#[derive(Debug, Eq, Hash, PartialEq)]
// Constraints either assign concrete types to type variables
// or set them equal to other type variables
pub enum TypeExpr {
    Concrete(u32, annotation_ir::Type),
    Variable(u32, u32),
}

fn generate_constraints(
    annotations: &AnnotationEnv,
    tree: &RuleParseTree,
    curr: &TypeVarNode,
    concrete_constraints: &mut HashSet<TypeExpr>,
    var_constraints: &mut HashSet<TypeExpr>,
) {
    if curr.children.len() == 0 {
        return;
    }

    let name = &curr.ident;
    let initial_types = get_initial_types(&name, &annotations);

    // TODO: make this not burn the eyes
    let ret_index = initial_types.len() - 1;
    for (i, var) in initial_types.iter().enumerate() {
        match var {
            // If we know the type of some var from the annotation, set it.
            Type::Known(ref t) => {
                if i == ret_index {
                    concrete_constraints.insert(TypeExpr::Concrete(
                        curr.type_var, t.clone())
                    );
                } else {
                    concrete_constraints.insert(TypeExpr::Concrete(
                        curr.children[i].type_var, t.clone())
                    );
                }
            }
            // If not, at least we know "relative polymorphic types."
            // If there's some other var with the same polymorphic type,
            // add a constraint that they must be equal.
            Type::Poly(_) => {
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
                            var_constraints.insert(
                                TypeExpr::Variable(curr.children[i].type_var, curr.type_var),
                            );
                        } else {
                            var_constraints.insert(TypeExpr::Variable(
                                curr.children[i].type_var,
                                curr.children[j].type_var,
                            ));
                        }
                    }
                }
            }
        }
    }

    for child in &curr.children {
        generate_constraints(&annotations, tree, &child, concrete_constraints, var_constraints);
    }
}

fn solve_constraints_help(
    concrete_constraints: &HashSet<TypeExpr>,
    var_constraints: &HashSet<TypeExpr>,
    results: &mut HashMap<u32, annotation_ir::Type>,
    num_vars: usize,
) {
    if results.len() == num_vars {
        return;
    }
    
    for c1 in var_constraints {
        match c1 {
            TypeExpr::Variable(m, n) => {
                if results.contains_key(&m) {
                    results.insert(*n, results[&m].clone());
                }

                if results.contains_key(&n) {
                    results.insert(*m, results[&n].clone());
                }
            }
            _ => panic!("Found concrete constraint in variable constraints list: {:#?}", c1),
        }
    }

    solve_constraints_help(concrete_constraints, var_constraints, results, num_vars);
}

fn solve_constraints(
    concrete_constraints: &HashSet<TypeExpr>,
    var_constraints: &HashSet<TypeExpr>,
    results: &mut HashMap<u32, annotation_ir::Type>,
    num_vars: usize,
) {
    for c in concrete_constraints {
        match c {
            TypeExpr::Concrete(type_var, concrete_type) => {
                results.insert(*type_var, concrete_type.clone());
            }
            _ => panic!("Found variable constraint in concrete constraints list: {:#?}", c),
        }
    }

    solve_constraints_help(concrete_constraints, var_constraints, results, num_vars);
}

fn type_annotations(
    tree: &RuleParseTree,
    sub: &HashMap<u32, annotation_ir::Type>,
) -> HashMap<String, Vec<annotation_ir::Type>> {
    let mut result = HashMap::new();
    for (term, type_vars) in &tree.term_to_type_var_map {
        let mut types = vec![];
        for type_var in type_vars {
            types.push(sub[&type_var].clone());
        }
        result.insert(term.clone(), types);
    }
    result
}