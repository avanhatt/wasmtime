use std::collections::{HashMap, HashSet};
use std::env;
use std::hash::Hash;
use std::path::PathBuf;

use cranelift_isle as isle;
use isle::ast::Def;
use isle::sema::{TermEnv, TermId, TypeEnv};
// use isle::sema::{Expr, Pattern, TermEnv, TermId, TypeEnv, TypeId, VarId};
use veri_annotation::parser_wrapper::{parse_annotations, AnnotationEnv};
use veri_ir::annotation_ir;

const REG_WIDTH: usize = 64;

fn main() {
    let cur_dir = env::current_dir().expect("Can't access current working directory");

    // let clif_isle = cur_dir.join("../../../codegen/src").join("clif.isle");
    // let prelude_isle = cur_dir.join("../../../codegen/src").join("prelude.isle");
    let input = cur_dir.join("files/ineg.isle");

    // let files = vec![input, clif_isle, prelude_isle];

    let files = vec![input];
    let lexer = isle::lexer::Lexer::from_files(&files).unwrap();
    let path_buf = PathBuf::from(&files[0]);
    let annotation_env = parse_annotations(&vec![path_buf]);
    let defs = isle::parser::parse(lexer).expect("should parse");
    let mut typeenv = isle::sema::TypeEnv::from_ast(&defs).unwrap();
    // We want to allow annotations on terms with internal extractors,
    // so we avoid expanding them within the sema rules.
    let termenv = isle::sema::TermEnv::from_ast(
        &mut typeenv,
        &defs,
        /* expand_internal_extractors */ false,
    )
    .unwrap();

    let mut defmap: HashMap<String, Def> = HashMap::new();
    for def in &defs.defs {
        match def {
            isle::ast::Def::Decl(ref d) => {
                let term = d.term.0.clone();
                defmap.insert(term, def.clone());
            }
            _ => continue,
        }
    }

    for rule in &termenv.rules {
        type_rule(&annotation_env, &termenv, &typeenv, &defmap, rule)
    }
}

#[derive(Debug, Eq, Hash, PartialEq)]
// Constraints either assign concrete types to type variables
// or set them equal to other type variables
enum TypeExpr {
    Concrete(u32, annotation_ir::Type),
    Variable(u32, u32),
}

#[derive(Debug)]
struct TypeContext<'ctx> {
    annenv: &'ctx AnnotationEnv,
    termenv: &'ctx TermEnv,
    typeenv: &'ctx TypeEnv,
    trees: Vec<annotation_ir::Expr>,
    next_type_var: u32,
    next_ann_idx: usize,
    concrete_constraints: HashSet<TypeExpr>,
    var_constraints: HashSet<TypeExpr>,
    bv_constraints: HashSet<TypeExpr>,
    var_to_type_var: HashMap<(usize, String), u32>,
}

fn add_argument_constraints(
    ty_ctx: &mut TypeContext,
    defmap: &HashMap<String, Def>,
    termid: &TermId,
    subterms: Vec<Option<u32>>,
) -> u32 {
    let term = &ty_ctx.termenv.terms[termid.index()];
    let term_name = &ty_ctx.typeenv.syms[term.name.index()];
    let annotation = &ty_ctx
        .annenv
        .get_annotation_for_term(term_name)
        .unwrap_or_else(|| panic!("expected term for {}", term_name));
    let ann_idx = type_annotation(ty_ctx, annotation.clone(), defmap.get(term_name).unwrap());

    let ret = ty_ctx
        .var_to_type_var
        .get(&(ann_idx, annotation.sig.ret.name.clone()))
        .unwrap();

    for (s, a) in subterms.iter().zip(&annotation.sig.args) {
        if let Some(tyvar) = s {
            let arg = ty_ctx
                .var_to_type_var
                .get(&(ann_idx, a.name.clone()))
                .unwrap();
            ty_ctx
                .var_constraints
                .insert(TypeExpr::Variable(*tyvar, *arg));
        }
    }
    // The return type variable
    *ret
}

fn type_pattern(
    ty_ctx: &mut TypeContext,
    defmap: &HashMap<String, Def>,
    pat: &isle::sema::Pattern,
) -> Option<u32> {
    match pat {
        // If we hit a bound wildcard, no need to add constraints
        isle::sema::Pattern::BindPattern(_, _, subpat) => match **subpat {
            isle::sema::Pattern::Wildcard(..) => None,
            _ => unimplemented!("Unexpected BindPattern {:?}", subpat),
        },

        // Constants and variables should have types determined from annotations
        isle::sema::Pattern::ConstInt(_, _)
        | isle::sema::Pattern::ConstPrim(_, _)
        | isle::sema::Pattern::Var(_, _) => None,

        // For terms, get the type variable for each argument (if it exists) and add a new constraint
        // equating the types of the value returned by that subpattern.
        isle::sema::Pattern::Term(_, termid, subpatterns) => {
            let subterms = subpatterns
                .iter()
                .map(|p| type_pattern(ty_ctx, defmap, p))
                .collect();
            Some(add_argument_constraints(ty_ctx, defmap, termid, subterms))
        }
        isle::sema::Pattern::And(_, subpatterns) => {
            let ty_vars: Vec<Option<u32>> = subpatterns
                .iter()
                .map(|p| type_pattern(ty_ctx, defmap, p))
                .collect();

            // Filter to Some results
            let ty_vars: Vec<&u32> = ty_vars.iter().filter_map(|p| p.as_ref()).collect();
            if ty_vars.is_empty() {
                return None;
            }

            // We assert all sub type constraints are equivalent to the first subexpression,
            // then return it.
            let first = *ty_vars[0];
            for (i, e) in ty_vars.iter().enumerate() {
                if i != 0 {
                    ty_ctx
                        .var_constraints
                        .insert(TypeExpr::Variable(first, **e));
                }
            }
            Some(first)
        }
        _ => unimplemented!("Unexpected Pattern {:?}", pat),
    }
}

fn type_sema_expr(
    ty_ctx: &mut TypeContext,
    defmap: &HashMap<String, Def>,
    expr: &isle::sema::Expr,
) -> Option<u32> {
    match expr {
        isle::sema::Expr::Var(..)
        | isle::sema::Expr::ConstInt(..)
        | isle::sema::Expr::ConstPrim(..) => None,
        isle::sema::Expr::Term(_, termid, subterms) => {
            let subterms = subterms
                .iter()
                .map(|p| type_sema_expr(ty_ctx, defmap, p))
                .collect();
            Some(add_argument_constraints(ty_ctx, defmap, termid, subterms))
        }
        isle::sema::Expr::Let {
            bindings: _,
            body: _,
            ..
        } => todo!(),
    }
}

fn type_rule(
    annotation_env: &AnnotationEnv,
    termenv: &TermEnv,
    typeenv: &TypeEnv,
    defmap: &HashMap<String, Def>,
    rule: &isle::sema::Rule,
) {
    let mut ctx = TypeContext {
        annenv: annotation_env,
        termenv,
        typeenv,
        trees: vec![],
        next_type_var: 1,
        next_ann_idx: 1,
        concrete_constraints: HashSet::new(),
        var_constraints: HashSet::new(),
        bv_constraints: HashSet::new(),
        var_to_type_var: HashMap::new(),
    };

    type_pattern(&mut ctx, defmap, &rule.lhs);
    type_sema_expr(&mut ctx, defmap, &rule.rhs);

    let res = solve_constraints(
        ctx.concrete_constraints,
        ctx.var_constraints,
        ctx.bv_constraints,
    );

    println!("{:#?}", res);
}

// generate constraints for each expr and solve
fn type_annotation(
    ty_ctx: &mut TypeContext,
    a: annotation_ir::TermAnnotation,
    d: &isle::ast::Def,
) -> usize {
    let ann_idx = ty_ctx.next_ann_idx;
    ty_ctx.next_ann_idx += 1;
    for e in a.assertions {
        let tree = generate_expr_constraints(*e, ty_ctx, ann_idx);
        ty_ctx.trees.push(tree);
        add_isle_constraints(d.clone(), ty_ctx, a.sig.clone(), ann_idx);
    }
    ann_idx
}

fn generate_expr_constraints(
    expr: annotation_ir::Expr,
    trees: &mut TypeContext,
    ann_idx: usize,
) -> annotation_ir::Expr {
    match expr {
        annotation_ir::Expr::Var(x, ..) => {
            let mut t = trees.next_type_var;
            if trees.var_to_type_var.contains_key(&(ann_idx, x.clone())) {
                t = trees.var_to_type_var[&(ann_idx, x.clone())];
            } else {
                trees.var_to_type_var.insert((ann_idx, x.clone()), t);
                trees.next_type_var += 1;
            }
            annotation_ir::Expr::Var(x, t)
        }
        annotation_ir::Expr::Const(c, ..) => {
            let t = trees.next_type_var;
            trees
                .concrete_constraints
                .insert(TypeExpr::Concrete(t, c.clone().ty));

            trees.next_type_var += 1;
            annotation_ir::Expr::Const(c, t)
        }
        annotation_ir::Expr::TyWidth(_) => {
            let t = trees.next_type_var;
            trees
                .concrete_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::Int));

            trees.next_type_var += 1;
            annotation_ir::Expr::TyWidth(t)
        }

        annotation_ir::Expr::Eq(x, y, _) => {
            let e1 = generate_expr_constraints(*x, trees, ann_idx);
            let e2 = generate_expr_constraints(*y, trees, ann_idx);

            let t1 = annotation_ir::Expr::get_type_var(&e1);
            let t2 = annotation_ir::Expr::get_type_var(&e2);
            let t = trees.next_type_var;

            trees
                .concrete_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::Bool));
            trees.var_constraints.insert(TypeExpr::Variable(t1, t2));

            trees.next_type_var += 1;
            annotation_ir::Expr::Eq(Box::new(e1), Box::new(e2), t)
        }
        annotation_ir::Expr::Lte(x, y, _) => {
            let e1 = generate_expr_constraints(*x, trees, ann_idx);
            let e2 = generate_expr_constraints(*y, trees, ann_idx);

            let t1 = annotation_ir::Expr::get_type_var(&e1);
            let t2 = annotation_ir::Expr::get_type_var(&e2);
            let t = trees.next_type_var;

            trees
                .concrete_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::Bool));
            trees.var_constraints.insert(TypeExpr::Variable(t1, t2));

            trees.next_type_var += 1;
            annotation_ir::Expr::Lte(Box::new(e1), Box::new(e2), t)
        }

        annotation_ir::Expr::BVNeg(x, _) => {
            let e1 = generate_expr_constraints(*x, trees, ann_idx);
            let t1 = annotation_ir::Expr::get_type_var(&e1);

            let t = trees.next_type_var;
            trees
                .bv_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::BitVector));
            trees
                .bv_constraints
                .insert(TypeExpr::Concrete(t1, annotation_ir::Type::BitVector));
            trees.var_constraints.insert(TypeExpr::Variable(t, t1));

            trees.next_type_var += 1;
            annotation_ir::Expr::BVNeg(Box::new(e1), t)
        }

        annotation_ir::Expr::BVAdd(x, y, _) => {
            let e1 = generate_expr_constraints(*x, trees, ann_idx);
            let e2 = generate_expr_constraints(*y, trees, ann_idx);

            let t1 = annotation_ir::Expr::get_type_var(&e1);
            let t2 = annotation_ir::Expr::get_type_var(&e2);
            let t = trees.next_type_var;

            trees
                .bv_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::BitVector));
            trees
                .bv_constraints
                .insert(TypeExpr::Concrete(t1, annotation_ir::Type::BitVector));
            trees
                .bv_constraints
                .insert(TypeExpr::Concrete(t2, annotation_ir::Type::BitVector));
            trees.var_constraints.insert(TypeExpr::Variable(t1, t2));
            trees.var_constraints.insert(TypeExpr::Variable(t, t1));
            trees.var_constraints.insert(TypeExpr::Variable(t, t2));

            trees.next_type_var += 1;
            annotation_ir::Expr::BVAdd(Box::new(e1), Box::new(e2), t)
        }
        annotation_ir::Expr::BVSub(x, y, _) => {
            let e1 = generate_expr_constraints(*x, trees, ann_idx);
            let e2 = generate_expr_constraints(*y, trees, ann_idx);

            let t1 = annotation_ir::Expr::get_type_var(&e1);
            let t2 = annotation_ir::Expr::get_type_var(&e2);
            let t = trees.next_type_var;

            trees
                .bv_constraints
                .insert(TypeExpr::Concrete(t, annotation_ir::Type::BitVector));
            trees
                .bv_constraints
                .insert(TypeExpr::Concrete(t1, annotation_ir::Type::BitVector));
            trees
                .bv_constraints
                .insert(TypeExpr::Concrete(t2, annotation_ir::Type::BitVector));
            trees.var_constraints.insert(TypeExpr::Variable(t1, t2));
            trees.var_constraints.insert(TypeExpr::Variable(t, t1));
            trees.var_constraints.insert(TypeExpr::Variable(t, t2));

            trees.next_type_var += 1;
            annotation_ir::Expr::BVSub(Box::new(e1), Box::new(e2), t)
        }

        annotation_ir::Expr::BVConvTo(w, x, _) => {
            let e1 = generate_expr_constraints(*x, trees, ann_idx);
            let t1 = annotation_ir::Expr::get_type_var(&e1);
            let t = trees.next_type_var;

            let width = match *w {
                annotation_ir::Width::Const(x) => x,
                annotation_ir::Width::RegWidth => REG_WIDTH,
            };

            trees.concrete_constraints.insert(TypeExpr::Concrete(
                t,
                annotation_ir::Type::BitVectorWithWidth(width),
            ));
            trees
                .bv_constraints
                .insert(TypeExpr::Concrete(t1, annotation_ir::Type::BitVector));

            trees.next_type_var += 1;
            annotation_ir::Expr::BVConvTo(w, Box::new(e1), t)
        }
        _ => todo!("expr {:#?} not yet implemented", expr),
    }
}

fn add_isle_constraints(
    def: isle::ast::Def,
    trees: &mut TypeContext,
    annotation: annotation_ir::TermSignature,
    ann_idx: usize,
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
                //println!("isle type: {}, annotation_var: {}", &isle_type, &annotation_var);
                // in case the var was not in the annotation
                if !trees
                    .var_to_type_var
                    .contains_key(&(ann_idx, annotation_var.clone()))
                {
                    trees
                        .var_to_type_var
                        .insert((ann_idx, annotation_var.clone()), trees.next_type_var);
                    trees.next_type_var += 1;
                }

                let ir_type = &clif_to_ir_types[isle_type];
                let type_var = trees.var_to_type_var[&(ann_idx, annotation_var)];
                match ir_type {
                    annotation_ir::Type::BitVector => trees
                        .bv_constraints
                        .insert(TypeExpr::Concrete(type_var, ir_type.clone())),
                    _ => trees
                        .concrete_constraints
                        .insert(TypeExpr::Concrete(type_var, ir_type.clone())),
                };
            }
        }
        _ => panic!("def must be decl, got: {:#?}", def),
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
                            if !union_find.contains_key(&t) {
                                union_find.insert(t.clone(), HashSet::new());
                            }
                            if let Some(group) = union_find.get_mut(&t) {
                                group.insert(v);
                            }

                            // if this type var also has a polymorphic type, union
                            if let Some(var_type) = get_var_type_poly(v, &union_find) {
                                let poly_bucket = union_find
                                    .remove(&var_type)
                                    .expect("expected key in union find");
                                let bv_bucket =
                                    union_find.get_mut(&t).expect("expected key in union find");
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
