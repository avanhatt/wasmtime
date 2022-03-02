/// This file handles renaming bound variables in assumption expressions,
/// which is necessary to use annotations that might share variable names.
use veri_ir::{BoundVar, FunctionAnnotation, VIRAnnotation, VIRExpr, DefinedSymbol};

pub fn rename_annotation_vars<F>(a: VIRAnnotation, rename: F) -> VIRAnnotation
where
    F: Fn(&BoundVar) -> BoundVar + Copy,
{
    let args = a.func().args.iter().map(|sym|{
        match sym {
            DefinedSymbol::Var(v) => DefinedSymbol::Var(rename(v)),
            DefinedSymbol::Function(..) => sym.clone(),
        }

    }).collect();
    let ret = rename(&a.func().ret);
    VIRAnnotation::new(
        FunctionAnnotation { args, ret },
        a.assertions()
            .iter()
            .map(|e| rename_vir_expr(e.clone(), rename))
            .collect(),
    )
}

fn rename_vir_expr<F>(expr: VIRExpr, rename: F) -> VIRExpr
where
    F: Fn(&BoundVar) -> BoundVar + Copy,
{
    let f = |x: Box<VIRExpr>| Box::new(rename_vir_expr(*x, rename));
    let map_f = |xs: Vec<VIRExpr>| {
        xs.iter()
            .map(|x| rename_vir_expr(x.clone(), rename))
            .collect()
    };
    match expr {
        VIRExpr::Const(..) | VIRExpr::True | VIRExpr::False | VIRExpr::Function(..) => expr,
        VIRExpr::Var(v) => VIRExpr::Var(rename(&v)),
        VIRExpr::Not(x) => VIRExpr::Not(f(x)),
        VIRExpr::And(x, y) => VIRExpr::And(f(x), f(y)),
        VIRExpr::Or(x, y) => VIRExpr::Or(f(x), f(y)),
        VIRExpr::Imp(x, y) => VIRExpr::Imp(f(x), f(y)),
        VIRExpr::Eq(x, y) => VIRExpr::Eq(f(x), f(y)),
        VIRExpr::Lte(x, y) => VIRExpr::Lte(f(x), f(y)),
        VIRExpr::BVNeg(ty, x) => VIRExpr::BVNeg(ty, f(x)),
        VIRExpr::BVNot(ty, x) => VIRExpr::BVNot(ty, f(x)),
        VIRExpr::BVAdd(ty, x, y) => VIRExpr::BVAdd(ty, f(x), f(y)),
        VIRExpr::BVSub(ty, x, y) => VIRExpr::BVSub(ty, f(x), f(y)),
        VIRExpr::BVAnd(ty, x, y) => VIRExpr::BVAnd(ty, f(x), f(y)),
        VIRExpr::BVZeroExt(ty, i, x) => VIRExpr::BVZeroExt(ty, i, f(x)),
        VIRExpr::BVSignExt(ty, i, x) => VIRExpr::BVSignExt(ty, i, f(x)),
        VIRExpr::BVExtract(ty, l, h, x) => VIRExpr::BVExtract(ty, l, h, f(x)),
        VIRExpr::FunctionApplication(ty, func, args) => {
            VIRExpr::FunctionApplication(ty, f(func), f(args))
        }
        VIRExpr::List(ty, xs) => VIRExpr::List(ty, map_f(xs)),
    }
}
