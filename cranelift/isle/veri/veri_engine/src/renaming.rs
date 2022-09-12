/// This file handles renaming bound variables in assumption expressions,
/// which is necessary to use annotations that might share variable names.
use veri_ir::{
    BoundVar, Expr, FunctionApplication, UndefinedTerm, VIRTermAnnotation, VIRTermSignature,
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

fn rename_vir_expr<F>(expr: Expr, rename: F) -> Expr
where
    F: Fn(&BoundVar) -> BoundVar + Copy,
{
    todo!()
    // let f = |x: Box<Expr>| Box::new(rename_vir_expr(*x, rename));
    // let map_f = |xs: Vec<Expr>| {
    //     xs.iter()
    //         .map(|x| rename_vir_expr(x.clone(), rename))
    //         .collect()
    // };
    // match expr {
    //     Expr::Const(..) | Expr::True | Expr::False => expr,
    //     // TODO: handle nested scope?
    //     Expr::Function(..) => expr,
    //     Expr::Var(v) => Expr::Var(rename(&v)),
    //     Expr::Not(x) => Expr::Not(f(x)),
    //     Expr::WidthOf(x) => Expr::WidthOf(f(x)),
    //     Expr::And(x, y) => Expr::And(f(x), f(y)),
    //     Expr::Or(x, y) => Expr::Or(f(x), f(y)),
    //     Expr::Imp(x, y) => Expr::Imp(f(x), f(y)),
    //     Expr::Eq(x, y) => Expr::Eq(f(x), f(y)),
    //     Expr::Lte(x, y) => Expr::Lte(f(x), f(y)),
    //     Expr::BVNeg(ty, x) => Expr::BVNeg(ty, f(x)),
    //     Expr::BVNot(ty, x) => Expr::BVNot(ty, f(x)),
    //     Expr::BVAdd(ty, x, y) => Expr::BVAdd(ty, f(x), f(y)),
    //     Expr::BVSub(ty, x, y) => Expr::BVSub(ty, f(x), f(y)),
    //     Expr::BVAnd(ty, x, y) => Expr::BVAnd(ty, f(x), f(y)),
    //     Expr::BVOr(ty, x, y) => Expr::BVOr(ty, f(x), f(y)),
    //     Expr::BVRotl(ty, x, y) => Expr::BVRotl(ty, f(x), f(y)),
    //     Expr::BVShl(ty, x, y) => Expr::BVShl(ty, f(x), f(y)),
    //     Expr::BVShr(ty, x, y) => Expr::BVShr(ty, f(x), f(y)),
    //     Expr::BVZeroExt(ty, i, x) => Expr::BVZeroExt(ty, i, f(x)),
    //     Expr::BVSignExt(ty, i, x) => Expr::BVSignExt(ty, i, f(x)),
    //     Expr::BVExtract(ty, l, h, x) => Expr::BVExtract(ty, l, h, f(x)),
    //     Expr::BVIntToBV(ty, x) => Expr::BVIntToBV(ty, f(x)),
    //     Expr::FunctionApplication(app) => Expr::FunctionApplication(FunctionApplication {
    //         ty: app.ty,
    //         func: f(app.func),
    //         args: map_f(app.args),
    //     }),
    //     Expr::UndefinedTerm(term) => Expr::UndefinedTerm(UndefinedTerm {
    //         name: term.name,
    //         ret: term.ret,
    //         args: map_f(term.args),
    //     }),
    //     Expr::List(ty, xs) => Expr::List(ty, map_f(xs)),
    //     Expr::GetElement(ty, ls, i) => Expr::GetElement(ty, f(ls), i),
    // }
}
