use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::path::PathBuf;

use cranelift_isle as isle;
use veri_annotation::parser_wrapper::{parse_annotations, AnnotationEnv};
use veri_ir::annotation_ir;

const REG_WIDTH: usize = 64;

fn main() {
	let files = vec!["files/ineg.isle"];
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
        var_to_type_var_map: HashMap::new(),
        next_type_var: 1,
        concrete_constraints: HashSet::new(),
        var_constraints: HashSet::new(),
        bv_constraints: HashSet::new(),
        decls: HashMap::new(),
    };
    for def in &defs.defs {
        parse_tree = match def {
            isle::ast::Def::Rule(r) => create_parse_tree(r.clone()),
            _ => continue,
        };
    }

    for def in defs.defs {
        match def {
            isle::ast::Def::Decl(d) => {
                parse_tree.decls.insert(d.term.0.clone(), d);
                /*let term = d.term.0.clone();
                println!("term {}", &term);
                let annotation = annotation_env.get_annotation_for_term(&term).unwrap();
                let types = type_annotation(annotation, def);
                println!("{:#?}", types);*/
            }
            _ => continue
        }        
    }
    //println!("[*] Created parse tree: {:#?}", parse_tree);
    
    // TODO: fix borrowing everywhere but this is the worst offender
    let copy = parse_tree.clone();
    add_rule_constraints(&mut parse_tree, &copy.lhs, &annotation_env);
    add_rule_constraints(&mut parse_tree, &copy.rhs, &annotation_env);
    parse_tree.var_constraints.insert(TypeExpr::Variable(
        parse_tree.lhs.type_var,
        parse_tree.rhs.type_var,
    ));
    //println!("{:#?}", &parse_tree);
    let types = solve_constraints(
        parse_tree.concrete_constraints,
        parse_tree.var_constraints,
        parse_tree.bv_constraints,
    );
    println!("{:#?}", types);

    /*
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
    */


    //println!("[*]Term to isle types: {:#?}", term_to_isle_types);
    /*
    let mut concrete_constraints = HashSet::new();
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

#[derive(Clone, Debug)]
struct RuleParseTree {
    lhs: TypeVarNode,
    rhs: TypeVarNode,
    // a map of var name to type variable, where var could be
    // Pattern::Var or var used in Pattern::BindPattern
    var_to_type_var_map: HashMap<String, u32>,
    // bookkeeping that tells the next unused type var
    next_type_var: u32,
    // combined constraints from all nodes
    concrete_constraints: HashSet<TypeExpr>,
    var_constraints: HashSet<TypeExpr>,
    bv_constraints: HashSet<TypeExpr>,
    // a map of terms in the rule to their isle ast decl
    decls: HashMap<String, isle::ast::Decl>,
}

#[derive(Clone, Debug)]
struct TypeVarNode {
    ident: String,
    type_var: u32,
    children: Vec<TypeVarNode>,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
// Constraints either assign concrete types to type variables
// or set them equal to other type variables
enum TypeExpr {
    Concrete(u32, annotation_ir::Type),
    Variable(u32, u32),
}

#[derive(Debug)]
struct AnnotationTypeInfo {
    // map of annotation variable to assigned type var
    var_to_type_var: HashMap<String, u32>,
}

// TODO: borrow properly
/*
fn type_annotation(
    a: annotation_ir::TermAnnotation,
    d: isle::ast::Def,
) -> HashMap<u32, annotation_ir::Type> {
    let mut trees = AnnotationTypeInfo {
        var_to_type_var: HashMap::new(),
    };
    for e in a.assertions {
        let tree = generate_expr_constraints(*e, &mut trees);
        trees.trees.push(tree);
        add_isle_constraints(d.clone(), &mut trees, a.sig.clone());
    }
    println!("{:#?}", trees);
    solve_constraints(trees.concrete_constraints, trees.var_constraints, trees.bv_constraints)
}
*/
// USE A FRESH ANNOTATION_INFO PER TERM (KEEP SAME PER ASSUMPTION)
fn add_annotation_constraints(
    expr: annotation_ir::Expr,
    tree: &mut RuleParseTree,
    annotation_info: &mut AnnotationTypeInfo,
) -> annotation_ir::Expr {
    match expr {
        annotation_ir::Expr::Var(x, ..) => {
            let mut t = tree.next_type_var;
            if annotation_info.var_to_type_var.contains_key(&x) {
                t = annotation_info.var_to_type_var[&x];
            } else {
                annotation_info.var_to_type_var.insert(x.clone(), t);
                tree.next_type_var += 1;
            }
            annotation_ir::Expr::Var(x, t)
        }
        annotation_ir::Expr::Const(c, ..) => {
            let t = tree.next_type_var;
            match c.ty {
                annotation_ir::Type::BitVector => {
                    tree.bv_constraints
                        .insert(TypeExpr::Concrete(t, c.ty.clone()));
                }
                _ => {
                    tree.concrete_constraints
                        .insert(TypeExpr::Concrete(t, c.ty.clone()));
                }
            }
            tree.next_type_var += 1;
            annotation_ir::Expr::Const(c, t)
        }
        annotation_ir::Expr::TyWidth(_) => {
            let t = tree.next_type_var;
            tree.concrete_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::Int));

            tree.next_type_var += 1;
            annotation_ir::Expr::TyWidth(t)
        }

        annotation_ir::Expr::Eq(x, y, _) => {
            let e1 = add_annotation_constraints(*x, tree, annotation_info);
            let e2 = add_annotation_constraints(*y, tree, annotation_info);

            let t1 = annotation_ir::Expr::get_type_var(&e1);
            let t2 = annotation_ir::Expr::get_type_var(&e2);
            let t = tree.next_type_var;

            tree.concrete_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::Bool));
            tree.var_constraints.insert(TypeExpr::Variable(t1, t2));

            tree.next_type_var += 1;
            annotation_ir::Expr::Eq(Box::new(e1), Box::new(e2), t)
        }
        annotation_ir::Expr::Lte(x, y, _) => {
            let e1 = add_annotation_constraints(*x, tree, annotation_info);
            let e2 = add_annotation_constraints(*y, tree, annotation_info);

            let t1 = annotation_ir::Expr::get_type_var(&e1);
            let t2 = annotation_ir::Expr::get_type_var(&e2);
            let t = tree.next_type_var;

            tree.concrete_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::Bool));
            tree.var_constraints.insert(TypeExpr::Variable(t1, t2));

            tree.next_type_var += 1;
            annotation_ir::Expr::Lte(Box::new(e1), Box::new(e2), t)
        }

        annotation_ir::Expr::BVNeg(x, _) => {
            let e1 = add_annotation_constraints(*x, tree, annotation_info);
            let t1 = annotation_ir::Expr::get_type_var(&e1);

            let t = tree.next_type_var;
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::BitVector));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t1, annotation_ir::Type::BitVector));
            tree.var_constraints.insert(TypeExpr::Variable(t, t1));

            tree.next_type_var += 1;
            annotation_ir::Expr::BVNeg(Box::new(e1), t)
        }

        annotation_ir::Expr::BVAdd(x, y, _) => {
            let e1 = add_annotation_constraints(*x, tree, annotation_info);
            let e2 = add_annotation_constraints(*y, tree, annotation_info);

            let t1 = annotation_ir::Expr::get_type_var(&e1);
            let t2 = annotation_ir::Expr::get_type_var(&e2);
            let t = tree.next_type_var;

            tree.bv_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::BitVector));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t1, annotation_ir::Type::BitVector));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t2, annotation_ir::Type::BitVector));
            tree.var_constraints.insert(TypeExpr::Variable(t1, t2));
            tree.var_constraints.insert(TypeExpr::Variable(t, t1));
            tree.var_constraints.insert(TypeExpr::Variable(t, t2));

            tree.next_type_var += 1;
            annotation_ir::Expr::BVAdd(Box::new(e1), Box::new(e2), t)
        }
        annotation_ir::Expr::BVSub(x, y, _) => {
            let e1 = add_annotation_constraints(*x, tree, annotation_info);
            let e2 = add_annotation_constraints(*y, tree, annotation_info);

            let t1 = annotation_ir::Expr::get_type_var(&e1);
            let t2 = annotation_ir::Expr::get_type_var(&e2);
            let t = tree.next_type_var;

            tree.bv_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::BitVector));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t1, annotation_ir::Type::BitVector));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t2, annotation_ir::Type::BitVector));
            tree.var_constraints.insert(TypeExpr::Variable(t1, t2));
            tree.var_constraints.insert(TypeExpr::Variable(t, t1));
            tree.var_constraints.insert(TypeExpr::Variable(t, t2));

            tree.next_type_var += 1;
            annotation_ir::Expr::BVSub(Box::new(e1), Box::new(e2), t)
        }

        annotation_ir::Expr::BVConvTo(w, x, _) => {
            let e1 = add_annotation_constraints(*x, tree, annotation_info);
            let t1 = annotation_ir::Expr::get_type_var(&e1);
            let t = tree.next_type_var;

            let width = match *w {
                annotation_ir::Width::Const(x) => x,
                annotation_ir::Width::RegWidth => REG_WIDTH,
            };

            tree.concrete_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::BitVectorWithWidth(width)));            
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t1, annotation_ir::Type::BitVector));

            tree.next_type_var += 1;
            annotation_ir::Expr::BVConvTo(w, Box::new(e1), t)
        }
        _ => todo!("expr {:#?} not yet implemented", expr),
    }
}

fn add_isle_constraints(
    def: isle::ast::Def,
    tree: &mut RuleParseTree,
    annotation_info: &mut AnnotationTypeInfo,
    annotation: annotation_ir::TermSignature,
) {
    let CLIF_TO_IR_TYPES = HashMap::from([
        ("Type".to_owned(), annotation_ir::Type::Int),
        ("Imm12".to_owned(), annotation_ir::Type::BitVectorWithWidth(12)),
        ("Imm64".to_owned(), annotation_ir::Type::BitVectorWithWidth(64)),
        ("ImmShift".to_owned(), annotation_ir::Type::BitVectorWithWidth(6)),
        ("ImmLogic".to_owned(), annotation_ir::Type::BitVectorWithWidth(12)),
        ("u64".to_owned(), annotation_ir::Type::BitVectorWithWidth(64)),
        ("u8".to_owned(), annotation_ir::Type::BitVectorWithWidth(8)),
        ("bool".to_owned(), annotation_ir::Type::Bool),
        ("MoveWideConst".to_owned(), annotation_ir::Type::BitVectorWithWidth(16)),
        ("OperandSize".to_owned(), annotation_ir::Type::BitVector),
        ("Reg".to_owned(), annotation_ir::Type::BitVector),
        ("Inst".to_owned(), annotation_ir::Type::BitVector),
        ("Value".to_owned(), annotation_ir::Type::BitVector),
        ("ValueRegs".to_owned(), annotation_ir::Type::BitVector),
        ("InstOutput".to_owned(), annotation_ir::Type::BitVector),
    ]);    
    
    let mut annotation_vars = vec!();
    for a in annotation.args { annotation_vars.push(a.name); }
    annotation_vars.push(annotation.ret.name);

    match def {
        isle::ast::Def::Decl(d) => {
            let mut isle_types = vec!();
            for t in d.arg_tys { isle_types.push(t.0); }
            isle_types.push(d.ret_ty.0);
            assert_eq!(annotation_vars.len(), isle_types.len());

            for (isle_type, annotation_var) in isle_types.iter().zip(annotation_vars) {
                // in case the var was not in the annotation
                if !annotation_info.var_to_type_var.contains_key(&annotation_var) {
                    annotation_info.var_to_type_var.insert(
                        annotation_var.clone(), 
                        tree.next_type_var,
                    );
                    tree.next_type_var += 1;
                }

                let ir_type = &CLIF_TO_IR_TYPES[isle_type];
                let type_var = annotation_info.var_to_type_var[&annotation_var];
                match ir_type {
                    annotation_ir::Type::BitVector => 
                        tree.bv_constraints
                            .insert(TypeExpr::Concrete(type_var, ir_type.clone())),
                    _ => 
                        tree.concrete_constraints
                            .insert(TypeExpr::Concrete(type_var, ir_type.clone())),
                };
            }
        }
        _ => panic!("def must be decl, got: {:#?}", def)
    }
}

fn add_rule_constraints(
    tree: &mut RuleParseTree,
    curr: &TypeVarNode,
    annotation_env: &AnnotationEnv,
) {
    // only process terms, and exclude vars
    if !tree.decls.contains_key(&curr.ident) {
        return;
    }

    let annotation = annotation_env.get_annotation_for_term(&curr.ident).unwrap();

    // use a fresh mapping for each term
    // keep the same mapping between assertions in the same annotation
    let mut annotation_info = AnnotationTypeInfo {
        var_to_type_var: HashMap::new(),
    };
    for expr in annotation.assertions {
        add_annotation_constraints(*expr, tree, &mut annotation_info);
        add_isle_constraints(
            cranelift_isle::ast::Def::Decl(tree.decls[&curr.ident].clone()),
            tree,
            &mut annotation_info,
            annotation.sig.clone(),
        );
    }

    println!("{}: {:#?}", &curr.ident, &annotation_info.var_to_type_var);

    // set args in rule equal to args in annotation
    for (i, child) in curr.children.iter().enumerate() {
        let rule_type_var = child.type_var;
        let annotation_type_var = 
            annotation_info.var_to_type_var[&annotation.sig.args[i].name];
        tree.var_constraints.insert(TypeExpr::Variable(
            rule_type_var,
            annotation_type_var,
        ));
    }
    // set term ret var equal to annotation ret var
    tree.var_constraints
        .insert(TypeExpr::Variable(
            curr.type_var, 
            annotation_info.var_to_type_var[&annotation.sig.ret.name],
        ));

    for child in &curr.children {
        add_rule_constraints(tree, child, annotation_env);
    }
}

// Solve constraints as follows:
//   - process concrete constraints first
//   - then process variable constraints
//   - constraints involving bv without widths are last priority
//
// for example:
//   t2 = bv16
//   t3 = bv8
//
//   t5 = t4
//   t6 = t1
//   t3 = t4
//   t1 = t2
//   t7 = t8
//
//   t4 = bv
//   t1 = bv
//   t7 = bv
// 
// would result in:
//   bv16 -> t2, t6, t1
//   bv8 -> t3, t5, t4
//   poly(0) -> t5, t4 (intermediate group that gets removed)
//   poly(1) -> t6, t1 (intermediate group that gets removed)
//   poly(2) -> t7, t8 (intermediate group that gets removed)
//   bv -> t7, t8

// TODO: clean up
fn solve_constraints(
    concrete: HashSet<TypeExpr>,
    var: HashSet<TypeExpr>,
    bv: HashSet<TypeExpr>,
) -> HashMap<u32, annotation_ir::Type> {
    // maintain a union find that maps types to sets of type vars that have that type
    let mut union_find = HashMap::new();
    let mut poly = 0;

    // initialize union find with groups corresponding to concrete constraints
    for c in concrete {
        match c {
            TypeExpr::Concrete(v, t) => {
                if !union_find.contains_key(&t) {
                    union_find.insert(t.clone(), HashSet::new());
                }
                if let Some(group) = union_find.get_mut(&t) {
                    group.insert(v);
                }
            }
            _ => panic!(
                "Non-concrete constraint found in concrete constraints: {:#?}",
                c
            ),
        };
    }

    // process variable constraints as follows:
    //   if t1 = t2 and only t1 has been typed, add t2 to the same set as t1
    //   if t1 = t2 and only t2 has been typed, add t1 to the same set t2
    //   if t1 = t2 and neither has been typed, create a new poly type and add both to the set
    //   if t1 = t2 and both have been typed, union appropriately
    for v in var {
        match v {
            TypeExpr::Variable(v1, v2) => {
                let t1 = get_var_type(v1, &union_find);
                let t2 = get_var_type(v2, &union_find);

                match (t1, t2) {
                    (Some(x), Some(y)) => {
                        match (x.is_poly(), y.is_poly()) {
                            (false, false) => {
                                if x != y {
                                    panic!(
                                        "type conflict at constraint {:#?}: t{} has type {:#?}, t{} has type {:#?}",
                                        v, v1, x, v2, y 
                                    )
                                }
                            }
                            // union t1 and t2, keeping t2 as the leader
                            (true, false) => {
                                let g1 = union_find.remove(&x).expect("expected key in union find");
                                let g2 =
                                    union_find.get_mut(&y).expect("expected key in union find");
                                g2.extend(g1.iter());
                            }
                            // union t1 and t2, keeping t1 as the leader
                            (_, true) => {
                                // guard against the case where x and y have the same poly type
                                // so we remove the key and can't find it in the next line
                                if x != y {
                                    let g2 = union_find.remove(&y).expect("expected key in union find");
                                    let g1 =
                                        union_find.get_mut(&x).expect("expected key in union find");
                                    g1.extend(g2.iter());
                                }
                            }
                        };
                    }
                    (Some(x), None) => {
                        if let Some(group) = union_find.get_mut(&x) {
                            group.insert(v2);
                        }
                    }
                    (None, Some(x)) => {
                        if let Some(group) = union_find.get_mut(&x) {
                            group.insert(v1);
                        }
                    }
                    (None, None) => {
                        let t = annotation_ir::Type::Poly(poly);
                        union_find.insert(t.clone(), HashSet::new());
                        if let Some(group) = union_find.get_mut(&t) {
                            group.insert(v1);
                            group.insert(v2);
                        }
                        poly += 1;
                    }
                }
            }
            _ => panic!("Non-variable constraint found in var constraints: {:#?}", v),
        }
    }

    for b in bv {
        match b {
            TypeExpr::Concrete(v, ref t) => {
                match t {
                    annotation_ir::Type::BitVector => {
                        // if there's a bv constraint and the var has already 
                        // been typed (with a width), ignore the constraint
                        if let Some(var_type) = get_var_type_concrete(v, &union_find) {
                            match var_type {
                                annotation_ir::Type::BitVectorWithWidth(_) => {
                                    continue;
                                }
                                _ => panic!("Var was already typed as {:#?} but currently processing constraint: {:#?}", var_type, b),
                            }
                        
                        // otherwise add it to a generic bv bucket
                        } else {
                            if !union_find.contains_key(&t) {
                                union_find.insert(t.clone(), HashSet::new());
                            }
                            if let Some(group) = union_find.get_mut(&t) {
                                group.insert(v);
                            }

                            // if this type var also has a polymorphic type, union
                            if let Some(var_type) = get_var_type_poly(v, &union_find) {
                                let poly_bucket = union_find.remove(&var_type).expect("expected key in union find");
                                let bv_bucket =
                                    union_find.get_mut(&t).expect("expected key in union find");
                                bv_bucket.extend(poly_bucket.iter());
                            }
                        }
                    }
                    _ => panic!("Non-bv constraint found in bv constraints: {:#?}", b),
                }
            }
            TypeExpr::Variable(_, _) => panic!("Non-bv constraint found in bv constraints: {:#?}", b),
        }
    }

    let mut result = HashMap::new();
    for (t, vars) in union_find {
        for var in vars {
            result.insert(var, t.clone());
        }
    }
    result
}

// if the union find already contains the type var, return its type
// otherwise return None
fn get_var_type(
    t: u32,
    u: &HashMap<annotation_ir::Type, HashSet<u32>>,
) -> Option<annotation_ir::Type> {
    for (ty, vars) in u {
        if vars.contains(&t) {
            return Some(ty.clone());
        }
    }
    None
}

// If the union find contains the type var and it has a non-polymorphic, specific type
// return it. Otherwise return None.
fn get_var_type_concrete(
    t: u32,
    u: &HashMap<annotation_ir::Type, HashSet<u32>>,
) -> Option<annotation_ir::Type> {
    for (ty, vars) in u {
        match ty {
            annotation_ir::Type::Poly(_) | annotation_ir::Type::BitVector => continue,
            _ => {
                if vars.contains(&t) {
                    return Some(ty.clone());
                }
            }
        }
    }
    None
}

// If the union find contains the type var and it has a polymorphic type,
// return the polymorphic type. Otherwise return None.
fn get_var_type_poly(
    t: u32,
    u: &HashMap<annotation_ir::Type, HashSet<u32>>,
) -> Option<annotation_ir::Type> {
    for (ty, vars) in u {
        match ty {
            annotation_ir::Type::Poly(_) => {
                if vars.contains(&t) {
                    return Some(ty.clone());
                }
            }
            _ => continue
        }
    }
    None
}

fn create_parse_tree(rule: isle::ast::Rule) -> RuleParseTree {
    // TODO: clean up
    let mut tree = RuleParseTree {
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
        var_to_type_var_map: HashMap::new(),
        next_type_var: 1,
        concrete_constraints: HashSet::new(),
        var_constraints: HashSet::new(),
        bv_constraints: HashSet::new(),
        decls: HashMap::new(),
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
            for arg in args {
                let child = create_parse_tree_pattern(arg, tree);
                children.push(child);
            }
            let type_var = tree.next_type_var;
            tree.next_type_var += 1;

            TypeVarNode{
                ident: sym.0,
                type_var: type_var,
                children: children,
            }
        }
        isle::ast::Pattern::Var{ var, .. } => {
            let ident = var.0;

            tree.var_to_type_var_map.entry(ident.clone()).or_insert(tree.next_type_var);
            let type_var = tree.var_to_type_var_map[&ident];
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
            tree.var_to_type_var_map.insert(var.0, subpat_node.type_var);
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
            // process children first
            let mut children = vec![];
            for arg in args {
                let child = create_parse_tree_expr(arg, tree);
                children.push(child);
            }
            let type_var = tree.next_type_var;
            tree.next_type_var += 1;

            TypeVarNode{
                ident: sym.0,
                type_var: type_var,
                children: children,
            }
        }
        isle::ast::Expr::Var{ name, .. } => {
            // This case doesn't really change anything since we should
            // have already typed vars in the LHS, but it does check
            // that we aren't using a variable that wasn't declared.
            let ident = name.0;
            if !tree.var_to_type_var_map.contains_key(&ident) {
                panic!("var {} used in RHS that was not declared in LHS", &ident);
            }
            let type_var = tree.var_to_type_var_map[&ident];
            TypeVarNode{
                ident: ident.clone(),
                type_var: type_var,
                children: vec![],
            }
        }
        isle::ast::Expr::ConstPrim{ val, .. } => {
            let type_var = tree.next_type_var;
            tree.next_type_var += 1;
            TypeVarNode{
                ident: val.0,
                type_var: type_var,
                children: vec![],
            }
        }
        _ => todo!("parse tree expr: {:#?}", expr)
    }
}
/*
// #[derive(Clone, Debug, Eq, Hash, PartialEq)]
// pub enum Type {
//     Poly(u32),
//     Known(annotation_ir::Type),
// }

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
*/
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

// TODO mod tests?
#[test] 
fn test_solve_constraints() {
    // simple with specific and generic bvs
    let concrete = HashSet::from([
        TypeExpr::Concrete(2, annotation_ir::Type::BitVectorWithWidth(16)),
        TypeExpr::Concrete(3, annotation_ir::Type::BitVectorWithWidth(8)),
    ]);
    let var = HashSet::from([
        TypeExpr::Variable(5, 4),
        TypeExpr::Variable(6, 1),
        TypeExpr::Variable(3, 4),
        TypeExpr::Variable(1, 2),
    ]);
    let bv = HashSet::from([
        TypeExpr::Concrete(1, annotation_ir::Type::BitVector),
        TypeExpr::Concrete(4, annotation_ir::Type::BitVector),
    ]);
    let expected = HashMap::from([
        (1, annotation_ir::Type::BitVectorWithWidth(16)),
        (2, annotation_ir::Type::BitVectorWithWidth(16)),
        (3, annotation_ir::Type::BitVectorWithWidth(8)),
        (4, annotation_ir::Type::BitVectorWithWidth(8)),
        (5, annotation_ir::Type::BitVectorWithWidth(8)),
        (6, annotation_ir::Type::BitVectorWithWidth(16)),
    ]);
    assert_eq!(expected, solve_constraints(concrete, var, bv));

    // slightly more complicated with specific and generic bvs
    let concrete = HashSet::from([
        TypeExpr::Concrete(2, annotation_ir::Type::BitVectorWithWidth(16)),
        TypeExpr::Concrete(3, annotation_ir::Type::BitVectorWithWidth(8)),
    ]);
    let var = HashSet::from([
        TypeExpr::Variable(5, 4),
        TypeExpr::Variable(6, 1),
        TypeExpr::Variable(3, 4),
        TypeExpr::Variable(1, 2),
        TypeExpr::Variable(7, 8),
    ]);
    let bv = HashSet::from([
        TypeExpr::Concrete(1, annotation_ir::Type::BitVector),
        TypeExpr::Concrete(4, annotation_ir::Type::BitVector),
        TypeExpr::Concrete(7, annotation_ir::Type::BitVector),
    ]);
    let expected = HashMap::from([
        (1, annotation_ir::Type::BitVectorWithWidth(16)),
        (2, annotation_ir::Type::BitVectorWithWidth(16)),
        (3, annotation_ir::Type::BitVectorWithWidth(8)),
        (4, annotation_ir::Type::BitVectorWithWidth(8)),
        (5, annotation_ir::Type::BitVectorWithWidth(8)),
        (6, annotation_ir::Type::BitVectorWithWidth(16)),
        (7, annotation_ir::Type::BitVector),
        (8, annotation_ir::Type::BitVector),
    ]);
    assert_eq!(expected, solve_constraints(concrete, var, bv)); 
}

#[test]
#[should_panic]
fn test_solve_constraints_ill_typed() {
    // ill-typed
    let concrete = HashSet::from([
        TypeExpr::Concrete(2, annotation_ir::Type::BitVectorWithWidth(16)),
        TypeExpr::Concrete(3, annotation_ir::Type::BitVectorWithWidth(8)),
    ]);
    let var = HashSet::from([
        TypeExpr::Variable(5, 4),
        TypeExpr::Variable(6, 1),
        TypeExpr::Variable(4, 6),
        TypeExpr::Variable(3, 4),
        TypeExpr::Variable(1, 2),
    ]);
    let bv = HashSet::from([
        TypeExpr::Concrete(1, annotation_ir::Type::BitVector),
        TypeExpr::Concrete(4, annotation_ir::Type::BitVector),
    ]);
    solve_constraints(concrete, var, bv);
}