/// This file handles renaming bound variables in assumption expressions,
/// which is necessary to use annotations that might share variable names.
use veri_ir::{
    BoundVar, FunctionApplication, UndefinedTerm, VIRExpr, VIRTermAnnotation, VIRTermSignature,
};

pub fn rename_annotation_vars<F>(a: VIRTermAnnotation, rename: F) -> VIRTermAnnotation
where
    F: Fn(&BoundVar) -> BoundVar + Copy,
{
    let args = a.func().args.iter().map(rename).collect();
    let ret = rename(&a.func().ret);
    VIRTermAnnotation::new(
        VIRTermSignature { args, ret },
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
        VIRExpr::Const(..) | VIRExpr::True | VIRExpr::False => expr,
        // TODO: handle nested scope?
        VIRExpr::Function(..) => expr,
        VIRExpr::Var(v) => VIRExpr::Var(rename(&v)),
        VIRExpr::Not(x) => VIRExpr::Not(f(x)),
        VIRExpr::WidthOf(x) => VIRExpr::WidthOf(f(x)),
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
        VIRExpr::BVOr(ty, x, y) => VIRExpr::BVOr(ty, f(x), f(y)),
        VIRExpr::BVRotl(ty, x, y) => VIRExpr::BVRotl(ty, f(x), f(y)),
        VIRExpr::BVShl(ty, x, y) => VIRExpr::BVShl(ty, f(x), f(y)),
        VIRExpr::BVShr(ty, x, y) => VIRExpr::BVShr(ty, f(x), f(y)),
        VIRExpr::BVConvTo(ty, x, y) => VIRExpr::BVConvTo(ty, f(x), f(y)),
        VIRExpr::BVConvToSigned(ty, x, y) => VIRExpr::BVConvToSigned(ty, f(x), f(y)),
        VIRExpr::BVZeroExt(ty, i, x) => VIRExpr::BVZeroExt(ty, i, f(x)),
        VIRExpr::BVSignExt(ty, i, x) => VIRExpr::BVSignExt(ty, i, f(x)),
        VIRExpr::BVExtract(ty, l, h, x) => VIRExpr::BVExtract(ty, l, h, f(x)),
        VIRExpr::BVIntToBV(ty, x) => VIRExpr::BVIntToBV(ty, f(x)),
        VIRExpr::Conditional(ty, x, y, z) => VIRExpr::Conditional(ty, f(x), f(y), f(z)),
        VIRExpr::FunctionApplication(app) => VIRExpr::FunctionApplication(FunctionApplication {
            ty: app.ty,
            func: f(app.func),
            args: map_f(app.args),
        }),
        VIRExpr::UndefinedTerm(term) => VIRExpr::UndefinedTerm(UndefinedTerm {
            name: term.name,
            ret: term.ret,
            args: map_f(term.args),
        }),
        VIRExpr::List(ty, xs) => VIRExpr::List(ty, map_f(xs)),
        VIRExpr::GetElement(ty, ls, i) => VIRExpr::GetElement(ty, f(ls), i),
    }
}
