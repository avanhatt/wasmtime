use std::collections::{HashMap, HashSet};
use std::path::PathBuf;
use std::thread::current;

use cranelift_isle as isle;
use veri_annotation::parser_wrapper::{parse_annotations, AnnotationEnv};
use veri_ir::annotation_ir;

const REG_WIDTH: usize = 64;

fn main() {
	let files = vec!["files/uextend.isle"];
	let lexer = isle::lexer::Lexer::from_files(&files).unwrap();
    let path_buf = PathBuf::from(&files[0]);
    let annotation_env = parse_annotations(&vec![path_buf]);
    let defs = isle::parser::parse(lexer).expect("should parse");

    // for (term, _) in &annotation_env.annotation_map {
    //     let types = get_initial_types(term, &annotation_env, &term_to_isle_types[term]);
    //     println!("[*] Initial types for term {}: {:#?}", term, types);
    // }
    
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
        term_to_isle_type_map: HashMap::new(),
    };
	for def in &defs.defs {
        parse_tree = match def {
            isle::ast::Def::Rule(r) => create_parse_tree(r.clone()),
            _ => continue,
        };
	}

    for def in &defs.defs {
        match def {
            isle::ast::Def::Decl(d) => {
                let term = &d.term.0;
                let mut types = vec!();
                for t in &d.arg_tys {
                    types.push(t.0.clone());
                }
                types.push(d.ret_ty.0.clone());
                parse_tree.term_to_isle_type_map.insert(term.clone(), types);
            }
            _ => continue
        }
    }

    println!("[*] Created parse tree: {:#?}", parse_tree);
    //println!("[*]Term to isle types: {:#?}", term_to_isle_types);
    
    /*let mut concrete_constraints = HashSet::new();
    let mut var_constraints = HashSet::new();
    generate_constraints(
        &annotation_env,
        &term_to_isle_types,
        &parse_tree,
        &parse_tree.lhs,
        &mut concrete_constraints,
        &mut var_constraints,
    );
    generate_constraints(
        &annotation_env,
        &term_to_isle_types,
        &parse_tree,
        &parse_tree.rhs,
        &mut concrete_constraints,
        &mut var_constraints,
    );
    //println!("[*] Concrete constraints: {:#?}", concrete_constraints);
    //println!("[*] Variable constraints: {:#?}", var_constraints);
    
    let mut sub = HashMap::new();
    solve_constraints(
        &concrete_constraints,
        &var_constraints,
        &mut sub,
        (parse_tree.next_type_var - 1).try_into().unwrap(),
    );
    //println!("[*] Found substitution: {:#?}", sub);

    let results = type_annotations(&parse_tree, &sub);
    //println!("[*] Final results: {:#?}", results);*/
}

#[derive(Debug)]
struct RuleParseTree {
    lhs: TypeVarNode,
    rhs: TypeVarNode,
    // a map of term or var name to type var
    type_var_map: HashMap<String, u32>,
    // bookkeeping that tells the next unused type var
    next_type_var: u32,
    // a map of term to array of type vars representing the
    // args and ret var of the term's annotation
    term_to_type_var_map: HashMap<String, Vec<u32>>,
    term_to_isle_type_map: HashMap<String, Vec<String>>,
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
        term_to_isle_type_map: HashMap::new(),
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
        isle::ast::Pattern::BindPattern{ var, subpat, .. } => {
            let subpat_node = create_parse_tree_pattern(*subpat, tree);
            tree.type_var_map.insert(var.0, subpat_node.type_var);
            subpat_node
        }
        _ => todo!("parse tree pattern: {:#?}", pattern)
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
        isle::ast::Expr::ConstPrim{ val, .. } => {
            let ident = val.0;
            
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
        _ => todo!("parse tree expr: {:#?}", expr)
    }
}

// #[derive(Clone, Debug, Eq, Hash, PartialEq)]
// pub enum Type {
//     Poly(u32),
//     Known(annotation_ir::Type),
// }

#[derive(Debug, Eq, Hash, PartialEq)]
// Constraints either assign concrete types to type variables
// or set them equal to other type variables
pub enum TypeExpr {
    Concrete(u32, annotation_ir::Type),
    Variable(u32, u32),
}

// TODO: rename to generate_constraints
// Recursive helper to determine the types of args and ret var of an annotation.
fn get_initial_types_help(
    rule_tree: &RuleParseTree,
    expr: &Box<annotation_ir::Expr>,
    curr_type: Option<annotation_ir::Type>,
    constraints: &mut HashSet<TypeExpr>,
) -> Option<annotation_ir::Type> {
    match &**expr {
        annotation_ir::Expr::Var(name) => {
            // On the way down, start with a general type and get more specific as
            // we encouter operators that enforce more strict type requirements.
            let _ = &constraints.insert(TypeExpr::Concrete(rule_tree.type_var_map[name], curr_type?));
            curr_type
        }
        annotation_ir::Expr::Const(c) => {
            Some(c.ty.clone())
        }
        annotation_ir::Expr::TyWidth => {
            Some(annotation_ir::Type::Int)
        }
        annotation_ir::Expr::WidthOf(x) => {
            get_initial_types_help(
                rule_tree,
                expr,
                Some(annotation_ir::Type::BitVector),
                constraints,
            );
            Some(annotation_ir::Type::BitVector)
        }
        annotation_ir::Expr::Eq(x, y) | annotation_ir::Expr::Lte(x, y) => {
            let t1 = get_initial_types_help(&x, &vars, curr_type.clone(), initial_types);
            let t2 = get_initial_types_help(&y, &vars, curr_type.clone(), initial_types);
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
        annotation_ir::Expr::BVNeg(x) => {
            get_initial_types_help(
                &x,
                &vars,
                Type::Known(annotation_ir::Type::BitVector),
                initial_types,
            );
            Type::Known(annotation_ir::Type::BitVector)
        }
        annotation_ir::Expr::BVAdd(x, y) | annotation_ir::Expr::BVSub(x, y) => {
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
        annotation_ir::Expr::BVConvTo(w, x) => {
            get_initial_types_help(
                &x,
                &vars,
                Type::Known(annotation_ir::Type::BitVector),
                initial_types,
            );

            let t = match **w {
                annotation_ir::Width::Const(c) => 
                    annotation_ir::Type::BitVectorWithWidth(c),
                annotation_ir::Width::RegWidth => 
                    annotation_ir::Type::BitVectorWithWidth(REG_WIDTH),
            };            
            Type::Known(t)
        }
        // TODO: type with the exact width
        annotation_ir::Expr::BVIntToBv(width, val) => {
            get_initial_types_help(
                &width,
                &vars,
                Type::Known(annotation_ir::Type::Int),
                initial_types,
            );
            get_initial_types_help(
                &val,
                &vars,
                Type::Known(annotation_ir::Type::Int),
                initial_types,
            );
            Type::Known(annotation_ir::Type::BitVector)
        }
        _ => todo!("initial types expr: {:#?}", expr)
    }
}
/*
// Return a vector containing the types of the args and ret var of the
// annotation on the given term. The type of the ret var is the last element.
// This function performs "type inference" using only the annotation and
// does not use any rules.
fn get_initial_types(
    term: &str,
    annotation_env: &AnnotationEnv,
    isle_types: &Vec<&str>,
) -> Vec<Type> {
    // First try getting bucket types
    let bucket_types = annotation_ir_type_for_type_id(isle_types);

    // Independently try to infer more specific types
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
    for i in 0..annotation.sig.args.len() {
        let arg = annotation.sig.args[i].clone();
        let bucket = bucket_types[i].clone();

        if !init.contains_key(&arg.name) {
            init.insert(arg.name.clone(), Type::Poly(0));
        }
        let inferred = init[&arg.name].clone();
        result.push(more_specific_type(inferred, Type::Known(bucket)));
    }

    let bucket = bucket_types[annotation.sig.args.len()].clone();
    if !init.contains_key(&annotation.sig.ret.name) {
        init.insert(annotation.sig.ret.name.clone(), Type::Poly(0));
    }
    let inferred = init[&annotation.sig.ret.name].clone();
    result.push(more_specific_type(inferred, Type::Known(bucket)));
   
    result
}

fn more_specific_type(a: Type, b: Type) -> Type {
    if a == b {
        return a;
    }

    match (&a, &b) {
        (Type::Poly(_), _) => b,
        (_, Type::Poly(_)) => a,
        (Type::Known(annotation_ir::Type::BitVectorWithWidth(_)), 
            Type::Known(annotation_ir::Type::BitVector)) => a,
        (Type::Known(annotation_ir::Type::BitVector), 
            Type::Known(annotation_ir::Type::BitVectorWithWidth(_))) => b,
        _ => unreachable!("{:#?}, {:#?}", a, b),
    }
}

pub fn annotation_ir_type_for_type_id(
    isle_types: &Vec<&str>,
) -> Vec<annotation_ir::Type> {
    let CLIF_TO_IR_TYPES = HashMap::from([
        ("Type", annotation_ir::Type::Int),
        ("Imm12", annotation_ir::Type::BitVectorWithWidth(12)),
        ("Imm64", annotation_ir::Type::BitVectorWithWidth(64)),
        ("ImmShift", annotation_ir::Type::BitVectorWithWidth(6)),
        ("ImmLogic", annotation_ir::Type::BitVectorWithWidth(12)),
        ("u64", annotation_ir::Type::BitVectorWithWidth(64)),
        ("u8", annotation_ir::Type::BitVectorWithWidth(8)),
        ("bool", annotation_ir::Type::Bool),
        ("MoveWideConst", annotation_ir::Type::BitVectorWithWidth(16)),
        ("OperandSize", annotation_ir::Type::BitVector),
        ("Reg", annotation_ir::Type::BitVectorWithWidth(REG_WIDTH)),
        ("Inst", annotation_ir::Type::BitVector),
        ("Value", annotation_ir::Type::BitVector),
        ("ValueRegs", annotation_ir::Type::BitVector),
    ]);

    let mut ir_types = vec!();
    for t in isle_types {
        ir_types.push(CLIF_TO_IR_TYPES[t].clone());
    }
    ir_types
}

// Construct some constraints that are either of the form t_i = <concrete type>
// or t_i = t_j.
fn generate_constraints(
    annotations: &AnnotationEnv,
    isle_types: &HashMap<&String, Vec<&str>>,
    tree: &RuleParseTree,
    curr: &TypeVarNode,
    concrete_constraints: &mut HashSet<TypeExpr>,
    var_constraints: &mut HashSet<TypeExpr>,
) {
    if curr.children.len() == 0 {
        return;
    }

    // TODO: we already have these types in main()
    let name = &curr.ident;
    let initial_types = get_initial_types(&name, &annotations, &isle_types[name]);

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
        generate_constraints(
            &annotations,
            isle_types,
            tree,
            &child,
            concrete_constraints,
            var_constraints,
        );
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
}*/