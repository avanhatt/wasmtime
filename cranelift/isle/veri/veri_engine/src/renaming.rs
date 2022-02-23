/// This file handles renaming bound variables in assumption expressions,
/// which is necessary to use annotations that might share variable names.

use veri_ir::{BoundVar, VIRAnnotation, VIRExpr};

pub fn rename_annotation_vars<F>(a: VIRAnnotation, rename: F) -> VIRAnnotation
where
    F: Fn(&BoundVar) -> BoundVar + Copy,
{
    let args = a.func.args.iter().map(rename).collect();
    let ret = rename(&a.func.ret);
    VIRAnnotation {
        func: veri_ir::FunctionAnnotation {
            args,
            ret,
        },
        assertions: a
            .assertions
            .iter()
            .map(|e| rename_vir_expr(e.clone(), rename))
            .collect(),
    }
}

fn rename_vir_expr<F>(expr: VIRExpr, rename: F) -> VIRExpr
where
    F: Fn(&BoundVar) -> BoundVar + Copy,
{
    let f = |x: Box<VIRExpr>| Box::new(rename_vir_expr(*x, rename));
    match expr {
        VIRExpr::Const(..) | VIRExpr::True | VIRExpr::False => expr,
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
    }
}