use std::collections::{BTreeMap, HashMap, HashSet};
use std::hash::Hash;
use std::path::PathBuf;

use cranelift_isle as isle;
use isle::ast::{Decl, Defs};
use isle::compile::create_envs;
use isle::sema::{Sym, TermEnv, TypeEnv, VarId};
use veri_annotation::parser_wrapper::{parse_annotations, AnnotationEnv};
use veri_ir::annotation_ir;

const REG_WIDTH: usize = 64;

fn main() {
    let cur_dir = env::current_dir().expect("Can't access current working directory");

    // TODO: clean up path logic
    let clif_isle = cur_dir.join("../../../codegen/src").join("clif.isle");
    let prelude_isle = cur_dir.join("../../../codegen/src").join("prelude.isle");

    // Disable for now to not have to consider all rules
    // let aarch64_isle = cur_dir.join("../../../codegen/src/isa/aarch64").join("inst.isle");

    let matches = Command::new("Verification Engine for ISLE")
        .arg(
            Arg::new("INPUT")
                .help("Sets the input file")
                .required(true)
                .index(1),
        )
        .get_matches();
    let input = PathBuf::from(matches.value_of("INPUT").unwrap());
    let inputs = vec![clif_isle, prelude_isle, input];

    let (typeenv, termenv) = isle_files_to_terms(&inputs);
    let annotation_env = parse_annotations(&inputs);

    let files = vec!["examples/uextend.isle"];
    let lexer = isle::lexer::Lexer::from_files(&files).unwrap();
    
    let defs = isle::parser::parse(lexer).expect("should parse");
    let decls = build_decl_map(defs);

    for r in &termenv.rules {
        let s = type_annotations_using_rule(r, &annotation_env, &decls, &typeenv, &termenv);
        for a in s.annotation_infos {
            println!("{}", a.term);
            for (var, type_var) in a.var_to_type_var {
                println!("{}: {:#?}", var, s.type_var_to_type[&type_var]);
            }
            println!();
        }
    }

    // For now, verify rules rooted in `lower`
    verify_rules_with_lhs_root("lower", &termenv, &typeenv, &annotation_env);
}

fn build_decl_map(defs: Defs) -> HashMap<String, Decl> {
    let mut decls = HashMap::new();
    for def in defs.defs {
        match def {
            isle::ast::Def::Decl(d) => {
                decls.insert(d.term.0.clone(), d);
            }
            _ => continue,
        }
    }
    decls
}

// for debugging and printing purposes
/*fn main() {
    let files = vec!["files/uextend.isle"];
    let lexer = isle::lexer::Lexer::from_files(&files).unwrap();
    let defs = isle::parser::parse(lexer).expect("should parse");
    let (typeenv, termenv) = create_envs(&defs).unwrap();
    println!("{:#?}", termenv);
}*/

#[derive(Clone, Debug)]
struct RuleParseTree<'a> {
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
    decls: &'a HashMap<String, isle::ast::Decl>,
}

#[derive(Clone, Debug)]
struct TypeVarNode {
    ident: String,
    type_var: u32,
    children: Vec<TypeVarNode>,
    assertions: Vec<annotation_ir::Expr>,
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
    term: String,
    var_to_type_var: HashMap<String, u32>,
}

#[derive(Debug)]
struct Solution {
    annotation_infos: Vec<AnnotationTypeInfo>,
    // map of type var to solved type
    type_var_to_type: HashMap<u32, annotation_ir::Type>,
}

// TODO: borrow properly
fn type_annotations_using_rule(
    rule: &isle::sema::Rule,
    annotation_env: &AnnotationEnv,
    decls: &HashMap<String, isle::ast::Decl>,
    typeenv: &TypeEnv,
    termenv: &TermEnv,
) -> Solution {
    let mut parse_tree = RuleParseTree {
        var_to_type_var_map: HashMap::new(),
        next_type_var: 1,
        concrete_constraints: HashSet::new(),
        var_constraints: HashSet::new(),
        bv_constraints: HashSet::new(),
        decls,
    };

    let var_map = &mut BTreeMap::new();
    rule.lhs.build_var_map(var_map);
    let lhs = &mut create_parse_tree_pattern(&rule.lhs, &mut parse_tree, var_map, typeenv, termenv);
    let rhs = &mut create_parse_tree_expr(&rule.rhs, &mut parse_tree, var_map, typeenv, termenv);

    let mut annotation_infos = vec![];
    add_rule_constraints(&mut parse_tree, lhs, annotation_env, &mut annotation_infos);
    add_rule_constraints(&mut parse_tree, rhs, annotation_env, &mut annotation_infos);
    parse_tree
        .var_constraints
        .insert(TypeExpr::Variable(lhs.type_var, rhs.type_var));

    let solution = solve_constraints(
        parse_tree.concrete_constraints,
        parse_tree.var_constraints,
        parse_tree.bv_constraints,
    );

    Solution {
        annotation_infos,
        type_var_to_type: solution,
    }
}

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
        annotation_ir::Expr::WidthOf(x, _) => {
            let ex = add_annotation_constraints(*x.clone(), tree, annotation_info);
            let tx = annotation_ir::Expr::get_type_var(&ex);
            let t = tree.next_type_var;
            tree.next_type_var += 1;
            tree.bv_constraints
                .insert(TypeExpr::Concrete(tx, annotation_ir::Type::BitVector));
            tree.concrete_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::Int));
            annotation_ir::Expr::WidthOf(x, t)
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

            tree.concrete_constraints.insert(TypeExpr::Concrete(
                t,
                annotation_ir::Type::BitVectorWithWidth(width),
            ));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t1, annotation_ir::Type::BitVector));

            tree.next_type_var += 1;
            annotation_ir::Expr::BVConvTo(w, Box::new(e1), t)
        }
        annotation_ir::Expr::BVIntToBv(x, w, _) => {
            let ex = add_annotation_constraints(*x.clone(), tree, annotation_info);
            let ew = add_annotation_constraints(*w.clone(), tree, annotation_info);

            let tx = annotation_ir::Expr::get_type_var(&ex);
            let tw = annotation_ir::Expr::get_type_var(&ew);

            let t = tree.next_type_var;
            tree.next_type_var += 1;

            tree.concrete_constraints
                .insert(TypeExpr::Concrete(tx, annotation_ir::Type::Int));
            tree.concrete_constraints
                .insert(TypeExpr::Concrete(tw, annotation_ir::Type::Int));
            tree.bv_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::BitVector));

            annotation_ir::Expr::BVIntToBv(x, w, t)
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
    let clif_to_ir_types = HashMap::from([
        ("Type".to_owned(), annotation_ir::Type::Int),
        (
            "Imm12".to_owned(),
            annotation_ir::Type::BitVectorWithWidth(12),
        ),
        (
            "Imm64".to_owned(),
            annotation_ir::Type::BitVectorWithWidth(64),
        ),
        (
            "ImmShift".to_owned(),
            annotation_ir::Type::BitVectorWithWidth(6),
        ),
        (
            "ImmLogic".to_owned(),
            annotation_ir::Type::BitVectorWithWidth(12),
        ),
        (
            "u64".to_owned(),
            annotation_ir::Type::BitVectorWithWidth(64),
        ),
        ("u8".to_owned(), annotation_ir::Type::BitVectorWithWidth(8)),
        ("bool".to_owned(), annotation_ir::Type::Bool),
        (
            "MoveWideConst".to_owned(),
            annotation_ir::Type::BitVectorWithWidth(16),
        ),
        ("OperandSize".to_owned(), annotation_ir::Type::BitVector),
        ("Reg".to_owned(), annotation_ir::Type::BitVector),
        ("Inst".to_owned(), annotation_ir::Type::BitVector),
        ("Value".to_owned(), annotation_ir::Type::BitVector),
        ("ValueRegs".to_owned(), annotation_ir::Type::BitVector),
        ("InstOutput".to_owned(), annotation_ir::Type::BitVector),
    ]);

    let mut annotation_vars = vec![];
    for a in annotation.args {
        annotation_vars.push(a.name);
    }
    annotation_vars.push(annotation.ret.name);

    match def {
        isle::ast::Def::Decl(d) => {
            let mut isle_types = vec![];
            for t in d.arg_tys {
                isle_types.push(t.0);
            }
            isle_types.push(d.ret_ty.0);
            assert_eq!(annotation_vars.len(), isle_types.len());

            for (isle_type, annotation_var) in isle_types.iter().zip(annotation_vars) {
                // in case the var was not in the annotation
                if !annotation_info
                    .var_to_type_var
                    .contains_key(&annotation_var)
                {
                    annotation_info
                        .var_to_type_var
                        .insert(annotation_var.clone(), tree.next_type_var);
                    tree.next_type_var += 1;
                }

                let ir_type = &clif_to_ir_types[isle_type];
                let type_var = annotation_info.var_to_type_var[&annotation_var];
                match ir_type {
                    annotation_ir::Type::BitVector => tree
                        .bv_constraints
                        .insert(TypeExpr::Concrete(type_var, ir_type.clone())),
                    _ => tree
                        .concrete_constraints
                        .insert(TypeExpr::Concrete(type_var, ir_type.clone())),
                };
            }
        }
        _ => panic!("def must be decl, got: {:#?}", def),
    }
}

fn add_rule_constraints(
    tree: &mut RuleParseTree,
    curr: &mut TypeVarNode,
    annotation_env: &AnnotationEnv,
    annotation_infos: &mut Vec<AnnotationTypeInfo>,
) {
    // only process terms, and exclude vars
    if !tree.decls.contains_key(&curr.ident) {
        return;
    }

    let annotation = annotation_env.get_annotation_for_term(&curr.ident).unwrap();

    // use a fresh mapping for each term
    // keep the same mapping between assertions in the same annotation
    let mut annotation_info = AnnotationTypeInfo {
        term: curr.ident.clone(),
        var_to_type_var: HashMap::new(),
    };
    for expr in annotation.assertions {
        let typed_expr = add_annotation_constraints(*expr, tree, &mut annotation_info);
        curr.assertions.push(typed_expr);
        add_isle_constraints(
            cranelift_isle::ast::Def::Decl(tree.decls[&curr.ident].clone()),
            tree,
            &mut annotation_info,
            annotation.sig.clone(),
        );
    }

    // set args in rule equal to args in annotation
    for (child, arg) in curr.children.iter().zip(&annotation.sig.args) {
        let rule_type_var = child.type_var;
        let annotation_type_var = annotation_info.var_to_type_var[&arg.name];
        tree.var_constraints
            .insert(TypeExpr::Variable(rule_type_var, annotation_type_var));
    }
    // set term ret var equal to annotation ret var
    tree.var_constraints.insert(TypeExpr::Variable(
        curr.type_var,
        annotation_info.var_to_type_var[&annotation.sig.ret.name],
    ));

    annotation_infos.push(annotation_info);

    for child in &mut curr.children {
        add_rule_constraints(tree, child, annotation_env, annotation_infos);
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
                                    let g2 =
                                        union_find.remove(&y).expect("expected key in union find");
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
                            if !union_find.contains_key(t) {
                                union_find.insert(t.clone(), HashSet::new());
                            }
                            if let Some(group) = union_find.get_mut(t) {
                                group.insert(v);
                            }

                            // if this type var also has a polymorphic type, union
                            if let Some(var_type) = get_var_type_poly(v, &union_find) {
                                let poly_bucket = union_find
                                    .remove(&var_type)
                                    .expect("expected key in union find");
                                let bv_bucket =
                                    union_find.get_mut(t).expect("expected key in union find");
                                bv_bucket.extend(poly_bucket.iter());
                            }
                        }
                    }
                    _ => panic!("Non-bv constraint found in bv constraints: {:#?}", b),
                }
            }
            TypeExpr::Variable(_, _) => {
                panic!("Non-bv constraint found in bv constraints: {:#?}", b)
            }
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
            _ => continue,
        }
    }
    None
}

fn create_parse_tree_pattern(
    pattern: &isle::sema::Pattern,
    tree: &mut RuleParseTree,
    var_map: &mut BTreeMap<VarId, Sym>,
    typeenv: &TypeEnv,
    termenv: &TermEnv,
) -> TypeVarNode {
    match pattern {
        isle::sema::Pattern::Term(_, term_id, args) => {
            let sym = termenv.terms[term_id.index()].name;
            let name = typeenv.syms[sym.index()].clone();

            // process children first
            let mut children = vec![];
            for arg in args {
                let child = create_parse_tree_pattern(arg, tree, var_map, typeenv, termenv);
                children.push(child);
            }
            let type_var = tree.next_type_var;
            tree.next_type_var += 1;

            TypeVarNode {
                ident: name,
                type_var,
                children,
                assertions: vec![],
            }
        }
        isle::sema::Pattern::Var(_, var_id) => {
            let sym = var_map[var_id];
            let ident = typeenv.syms[sym.index()].clone();

            tree.var_to_type_var_map
                .entry(ident.clone())
                .or_insert(tree.next_type_var);
            let type_var = tree.var_to_type_var_map[&ident];
            if type_var == tree.next_type_var {
                tree.next_type_var += 1;
            }

            // this is a base case so there are no children
            TypeVarNode {
                ident,
                type_var,
                children: vec![],
                assertions: vec![],
            }
        }
        isle::sema::Pattern::BindPattern(_, var_id, subpat) => {
            let sym = var_map[var_id];
            let var = typeenv.syms[sym.index()].clone();
            let subpat_node = create_parse_tree_pattern(subpat, tree, var_map, typeenv, termenv);
            tree.var_to_type_var_map.insert(var, subpat_node.type_var);
            subpat_node
        }
        isle::sema::Pattern::Wildcard(_, s) => {
            let mut name = String::from("wildcard");
            if let Some(sym) = s {
                name = typeenv.syms[sym.index()].clone();
            }
            let type_var = tree.next_type_var;
            tree.next_type_var += 1;
            TypeVarNode {
                ident: name,
                type_var,
                children: vec![],
                assertions: vec![],
            }
        }
        isle::sema::Pattern::ConstPrim(_, sym) => {
            let type_var = tree.next_type_var;
            tree.next_type_var += 1;
            TypeVarNode {
                ident: typeenv.syms[sym.index()].clone(),
                type_var,
                children: vec![],
                assertions: vec![],
            }
        }
        isle::sema::Pattern::ConstInt(_, num) => {
            let type_var = tree.next_type_var;
            tree.next_type_var += 1;
            TypeVarNode {
                ident: num.to_string(),
                type_var,
                children: vec![],
                assertions: vec![],
            }
        }
        isle::sema::Pattern::And(_, subpats) => {
            let mut children = vec![];
            let mut ty_vars = vec![];
            for p in subpats {
                let child = create_parse_tree_pattern(p, tree, var_map, typeenv, termenv);
                ty_vars.push(child.type_var);
                children.push(child);
            }
            let type_var = tree.next_type_var;
            tree.next_type_var += 1;

            // Assert all sub type constraints are equivalent to the first subexpression
            let first = ty_vars[0];
            for e in &ty_vars[1..] {
                tree.var_constraints
                    .insert(TypeExpr::Variable(first, e.to_owned()));
            }

            TypeVarNode {
                ident: String::from("and"),
                type_var,
                children,
                assertions: vec![],
            }
        }
    }
}

fn create_parse_tree_expr(
    expr: &isle::sema::Expr,
    tree: &mut RuleParseTree,
    var_map: &mut BTreeMap<VarId, Sym>,
    typeenv: &TypeEnv,
    termenv: &TermEnv,
) -> TypeVarNode {
    match expr {
        isle::sema::Expr::Term(_, term_id, args) => {
            let sym = termenv.terms[term_id.index()].name;
            let name = typeenv.syms[sym.index()].clone();

            // process children first
            let mut children = vec![];
            for arg in args {
                let child = create_parse_tree_expr(arg, tree, var_map, typeenv, termenv);
                children.push(child);
            }
            let type_var = tree.next_type_var;
            tree.next_type_var += 1;

            TypeVarNode {
                ident: name,
                type_var,
                children,
                assertions: vec![],
            }
        }
        isle::sema::Expr::Var(_, var_id) => {
            let mut ident = var_id.0.to_string();
            if !var_map.contains_key(var_id) {
                println!("var {} not found, using var id instead", var_id.0);
            } else {
                let sym = var_map[var_id];
                ident = typeenv.syms[sym.index()].clone();
            }

            tree.var_to_type_var_map
                .entry(ident.clone())
                .or_insert(tree.next_type_var);
            let type_var = tree.var_to_type_var_map[&ident];
            if type_var == tree.next_type_var {
                tree.next_type_var += 1;
            }

            // this is a base case so there are no children
            TypeVarNode {
                ident,
                type_var,
                children: vec![],
                assertions: vec![],
            }
        }
        isle::sema::Expr::ConstPrim(_, sym) => {
            let type_var = tree.next_type_var;
            tree.next_type_var += 1;
            TypeVarNode {
                ident: typeenv.syms[sym.index()].clone(),
                type_var,
                children: vec![],
                assertions: vec![],
            }
        }
        isle::sema::Expr::ConstInt(_, num) => {
            let type_var = tree.next_type_var;
            tree.next_type_var += 1;
            TypeVarNode {
                ident: num.to_string(),
                type_var,
                children: vec![],
                assertions: vec![],
            }
        }
        _ => todo!("parse tree expr: {:#?}", expr),
    }
}

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
