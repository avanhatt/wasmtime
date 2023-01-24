use crate::solver::SolverCtx;
use easy_smt::SExpr;

/*
pub fn rbit32(solver: &mut SolverCtx, x: SExpr, id: u32) -> SExpr {
    solver
        .additional_decls
        .push((format!("a64x_{id}", id = id), String::from("(_ BitVec 32)")));
    solver.additional_assumptions.push(format!(
        "(= a64x_{id} ((_ extract 31 0) {x}))",
        id = id,
        x = x
    ));

    solver
        .additional_decls
        .push((format!("x1_{id}", id = id), String::from("(_ BitVec 32)")));
    solver.additional_assumptions.push(format!(
        "(= x1_{id} (bvor (bvlshr a64x_{id} #x00000010) (bvshl a64x_{id} #x00000010)))",
        id = id
    ));

    solver
        .additional_decls
        .push((format!("x2_{id}", id = id), String::from("(_ BitVec 32)")));
    solver.additional_assumptions.push(format!("(= x2_{id} (bvor (bvlshr (bvand x1_{id} #xff00ff00) #x00000008) (bvshl (bvand x1_{id} #x00ff00ff) #x00000008)))", id = id));

    solver
        .additional_decls
        .push((format!("x3_{id}", id = id), String::from("(_ BitVec 32)")));
    solver.additional_assumptions.push(format!("(= x3_{id} (bvor (bvlshr (bvand x2_{id} #xf0f0f0f0) #x00000004) (bvshl (bvand x2_{id} #x0f0f0f0f) #x00000004)))", id = id));

    solver
        .additional_decls
        .push((format!("x4_{id}", id = id), String::from("(_ BitVec 32)")));
    solver.additional_assumptions.push(format!("(= x4_{id} (bvor (bvlshr (bvand x3_{id} #xcccccccc) #x00000002) (bvshl (bvand x3_{id} #x33333333) #x00000002)))", id = id));

    solver.additional_decls.push((
        format!("rbitret_{id}", id = id),
        String::from("(_ BitVec 32)"),
    ));
    solver.additional_assumptions.push(format!("(= rbitret_{id} (bvor (bvlshr (bvand x4_{id} #xaaaaaaaa) #x00000001) (bvshl (bvand x4_{id} #x55555555) #x00000001)))", id = id));

    let padding = solver.new_fresh_bits(solver.bitwidth - 32);
    format!(
        "(concat {padding} rbitret_{id})",
        padding = padding,
        id = id
    )
}
*/

pub fn rev64(solver: &mut SolverCtx, x: SExpr, id: u32) -> SExpr {
    // Generated code.
    let x1 = solver.declare(format!("x1_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(64)]));
    solver.assume(solver.smt.eq(x1, solver.smt.bvor(solver.smt.bvlshr(x, solver.smt.atom("#x0000000000000020")), solver.smt.bvshl(x, solver.smt.atom("#x0000000000000020")))));
    let x2 = solver.declare(format!("x2_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(64)]));
    solver.assume(solver.smt.eq(x2, solver.smt.bvor(solver.smt.bvlshr(solver.smt.bvand(x1, solver.smt.atom("#xffff0000ffff0000")), solver.smt.atom("#x0000000000000010")), solver.smt.bvshl(solver.smt.bvand(x1, solver.smt.atom("#x0000ffff0000ffff")), solver.smt.atom("#x0000000000000010")))));
    let x3 = solver.declare(format!("x3_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(64)]));
    solver.assume(solver.smt.eq(x3, solver.smt.bvor(solver.smt.bvlshr(solver.smt.bvand(x2, solver.smt.atom("#xff00ff00ff00ff00")), solver.smt.atom("#x0000000000000008")), solver.smt.bvshl(solver.smt.bvand(x2, solver.smt.atom("#x00ff00ff00ff00ff")), solver.smt.atom("#x0000000000000008")))));
    let x4 = solver.declare(format!("x4_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(64)]));
    solver.assume(solver.smt.eq(x4, solver.smt.bvor(solver.smt.bvlshr(solver.smt.bvand(x3, solver.smt.atom("#xf0f0f0f0f0f0f0f0")), solver.smt.atom("#x0000000000000004")), solver.smt.bvshl(solver.smt.bvand(x3, solver.smt.atom("#x0f0f0f0f0f0f0f0f")), solver.smt.atom("#x0000000000000004")))));
    let x5 = solver.declare(format!("x5_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(64)]));
    solver.assume(solver.smt.eq(x5, solver.smt.bvor(solver.smt.bvlshr(solver.smt.bvand(x4, solver.smt.atom("#xcccccccccccccccc")), solver.smt.atom("#x0000000000000002")), solver.smt.bvshl(solver.smt.bvand(x4, solver.smt.atom("#x3333333333333333")), solver.smt.atom("#x0000000000000002")))));
    let rev64ret = solver.declare(format!("rev64ret_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(64)]));
    solver.assume(solver.smt.eq(rev64ret, solver.smt.bvor(solver.smt.bvlshr(solver.smt.bvand(x5, solver.smt.atom("#xaaaaaaaaaaaaaaaa")), solver.smt.atom("#x0000000000000001")), solver.smt.bvshl(solver.smt.bvand(x5, solver.smt.atom("#x5555555555555555")), solver.smt.atom("#x0000000000000001")))));
        
    rev64ret
}

pub fn rev32(solver: &mut SolverCtx, x: SExpr, id: u32) -> SExpr {
    let x = solver.smt.extract(31, 0, x);

    // Generated code.
    let x1 = solver.declare(format!("x1_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(32)]));
    solver.assume(solver.smt.eq(x1, solver.smt.bvor(solver.smt.bvlshr(x, solver.smt.atom("#x00000010")), solver.smt.bvshl(x, solver.smt.atom("#x00000010")))));
    let x2 = solver.declare(format!("x2_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(32)]));
    solver.assume(solver.smt.eq(x2, solver.smt.bvor(solver.smt.bvlshr(solver.smt.bvand(x1, solver.smt.atom("#xff00ff00")), solver.smt.atom("#x00000008")), solver.smt.bvshl(solver.smt.bvand(x1, solver.smt.atom("#x00ff00ff")), solver.smt.atom("#x00000008")))));
    let x3 = solver.declare(format!("x3_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(32)]));
    solver.assume(solver.smt.eq(x3, solver.smt.bvor(solver.smt.bvlshr(solver.smt.bvand(x2, solver.smt.atom("#xf0f0f0f0")), solver.smt.atom("#x00000004")), solver.smt.bvshl(solver.smt.bvand(x2, solver.smt.atom("#x0f0f0f0f")), solver.smt.atom("#x00000004")))));
    let x4 = solver.declare(format!("x4_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(32)]));
    solver.assume(solver.smt.eq(x4, solver.smt.bvor(solver.smt.bvlshr(solver.smt.bvand(x3, solver.smt.atom("#xcccccccc")), solver.smt.atom("#x00000002")), solver.smt.bvshl(solver.smt.bvand(x3, solver.smt.atom("#x33333333")), solver.smt.atom("#x00000002")))));
    let rev32ret = solver.declare(format!("rev32ret_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(32)]));
    solver.assume(solver.smt.eq(rev32ret, solver.smt.bvor(solver.smt.bvlshr(solver.smt.bvand(x4, solver.smt.atom("#xaaaaaaaa")), solver.smt.atom("#x00000001")), solver.smt.bvshl(solver.smt.bvand(x4, solver.smt.atom("#x55555555")), solver.smt.atom("#x00000001")))));

    let padding = solver.new_fresh_bits(solver.bitwidth - 32);
    solver.smt.concat(padding, rev32ret)
}

pub fn rev16(solver: &mut SolverCtx, x: SExpr, id: u32) -> SExpr {
    let x = solver.smt.extract(15, 0, x);

    // Generated code.
    let x1 = solver.declare(format!("x1_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(16)]));
    solver.assume(solver.smt.eq(x1, solver.smt.bvor(solver.smt.bvlshr(x, solver.smt.atom("#x0008")), solver.smt.bvshl(x, solver.smt.atom("#x0008")))));
    let x2 = solver.declare(format!("x2_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(16)]));
    solver.assume(solver.smt.eq(x2, solver.smt.bvor(solver.smt.bvlshr(solver.smt.bvand(x1, solver.smt.atom("#xf0f0")), solver.smt.atom("#x0004")), solver.smt.bvshl(solver.smt.bvand(x1, solver.smt.atom("#x0f0f")), solver.smt.atom("#x0004")))));
    let x3 = solver.declare(format!("x3_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(16)]));
    solver.assume(solver.smt.eq(x3, solver.smt.bvor(solver.smt.bvlshr(solver.smt.bvand(x2, solver.smt.atom("#xcccc")), solver.smt.atom("#x0002")), solver.smt.bvshl(solver.smt.bvand(x2, solver.smt.atom("#x3333")), solver.smt.atom("#x0002")))));
    let rev16ret = solver.declare(format!("rev16ret_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(16)]));
    solver.assume(solver.smt.eq(rev16ret, solver.smt.bvor(solver.smt.bvlshr(solver.smt.bvand(x3, solver.smt.atom("#xaaaa")), solver.smt.atom("#x0001")), solver.smt.bvshl(solver.smt.bvand(x3, solver.smt.atom("#x5555")), solver.smt.atom("#x0001")))));

    let padding = solver.new_fresh_bits(solver.bitwidth - 16);
    solver.smt.concat(padding, rev16ret)
}

pub fn rev8(solver: &mut SolverCtx, x: SExpr, id: u32) -> SExpr {
    let x = solver.smt.extract(7, 0, x);

    // Generated code.
    let x1 = solver.declare(format!("x1_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(8)]));
    solver.assume(solver.smt.eq(x1, solver.smt.bvor(solver.smt.bvlshr(x, solver.smt.atom("#x04")), solver.smt.bvshl(x, solver.smt.atom("#x04")))));
    let x2 = solver.declare(format!("x2_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(8)]));
    solver.assume(solver.smt.eq(x2, solver.smt.bvor(solver.smt.bvlshr(solver.smt.bvand(x1, solver.smt.atom("#xcc")), solver.smt.atom("#x02")), solver.smt.bvshl(solver.smt.bvand(x1, solver.smt.atom("#x33")), solver.smt.atom("#x02")))));
    let rev8ret = solver.declare(format!("rev8ret_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(8)]));
    solver.assume(solver.smt.eq(rev8ret, solver.smt.bvor(solver.smt.bvlshr(solver.smt.bvand(x2, solver.smt.atom("#xaa")), solver.smt.atom("#x01")), solver.smt.bvshl(solver.smt.bvand(x2, solver.smt.atom("#x55")), solver.smt.atom("#x01")))));

    let padding = solver.new_fresh_bits(solver.bitwidth - 8);
    solver.smt.concat(padding, rev8ret)
}

pub fn rev1(solver: &mut SolverCtx, x: SExpr, id: u32) -> SExpr {
    let x = solver.smt.extract(0, 0, x);
    
    // Generated code.
    let rev1ret = solver.declare(format!("rev1ret_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(1)]));
    solver.assume(solver.smt.eq(rev1ret, x));

    let padding = solver.new_fresh_bits(solver.bitwidth - 1);
    solver.smt.concat(padding, rev1ret)
}

#[cfg(test)]
mod tests {
    use super::*;
    use veri_ir::TypeContext;
    use crate::solver::SolverCtx;
    use std::collections::HashMap;
    
    fn get_ctx() -> SolverCtx {
        let mut smt = easy_smt::ContextBuilder::new().build().unwrap();
        SolverCtx {
            smt: smt,
            tyctx: TypeContext {
                tyvars: HashMap::new(),
                tymap: HashMap::new(),
                tyvals: HashMap::new(),
                bv_unknown_width_sets: HashMap::new(),
            },
            bitwidth: 32,
            var_map: HashMap::new(),
            width_vars: HashMap::new(),
            width_assumptions: vec![],
            additional_decls: vec![],
            additional_assumptions: vec![],
            fresh_bits_idx: 0,
        }
    }
    
    fn check(ctx: &SolverCtx, expr: SExpr, expected: &str) {
        let expr_s = format!("{}", ctx.smt.display(expr));
        assert_eq!(expr_s, expected);
    }

    #[test]
    fn rev1_test() {
        let mut ctx = get_ctx();
        
        let x = ctx.smt.atom("x");
        let res = rev1(&mut ctx, x, 42);

        check(&ctx, res, "(concat fresh0 rev1ret_42)");
        check(&ctx, ctx.additional_decls[0].1, "(_ BitVec 1)");
        check(&ctx, ctx.additional_assumptions[0], "(= rev1ret_42 ((_ extract 0 0) x))");
    }
}
