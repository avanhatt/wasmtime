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

pub fn rev64(solver: &mut SolverCtx, x: SExpr, id: u32) -> SExpr {
    solver
        .additional_decls
        .push((format!("x1_{id}", id = id), String::from("(_ BitVec 64)")));
    solver.additional_assumptions.push(format!(
        "(= x1_{id} (bvor (bvlshr {x} #x0000000000000020) (bvshl {x} #x0000000000000020)))",
        id = id,
        x = x
    ));

    solver
        .additional_decls
        .push((format!("x2_{id}", id = id), String::from("(_ BitVec 64)")));
    solver.additional_assumptions.push(format!("(= x2_{id} (bvor (bvlshr (bvand x1_{id} #xffff0000ffff0000) #x0000000000000010) (bvshl (bvand x1_{id} #x0000ffff0000ffff) #x0000000000000010)))", id = id));

    solver
        .additional_decls
        .push((format!("x3_{id}", id = id), String::from("(_ BitVec 64)")));
    solver.additional_assumptions.push(format!("(= x3_{id} (bvor (bvlshr (bvand x2_{id} #xff00ff00ff00ff00) #x0000000000000008) (bvshl (bvand x2_{id} #x00ff00ff00ff00ff) #x0000000000000008)))", id = id));

    solver
        .additional_decls
        .push((format!("x4_{id}", id = id), String::from("(_ BitVec 64)")));
    solver.additional_assumptions.push(format!("(= x4_{id} (bvor (bvlshr (bvand x3_{id} #xf0f0f0f0f0f0f0f0) #x0000000000000004) (bvshl (bvand x3_{id} #x0f0f0f0f0f0f0f0f) #x0000000000000004)))", id = id));

    solver
        .additional_decls
        .push((format!("x5_{id}", id = id), String::from("(_ BitVec 64)")));
    solver.additional_assumptions.push(format!("(= x5_{id} (bvor (bvlshr (bvand x4_{id} #xcccccccccccccccc) #x0000000000000002) (bvshl (bvand x4_{id} #x3333333333333333) #x0000000000000002)))", id = id));

    solver.additional_decls.push((
        format!("rev64ret_{id}", id = id),
        String::from("(_ BitVec 64)"),
    ));
    solver.additional_assumptions.push(format!("(= rev64ret_{id} (bvor (bvlshr (bvand x5_{id} #xaaaaaaaaaaaaaaaa) #x0000000000000001) (bvshl (bvand x5_{id} #x5555555555555555) #x0000000000000001)))", id = id));

    format!("rev64ret_{id}", id = id)
}

pub fn rev32(solver: &mut SolverCtx, x: SExpr, id: u32) -> SExpr {
    let x = format!("((_ extract 31 0) {})", x);

    solver
        .additional_decls
        .push((format!("x1_{id}", id = id), String::from("(_ BitVec 32)")));
    solver.additional_assumptions.push(format!(
        "(= x1_{id} (bvor (bvlshr {x} #x00000010) (bvshl {x} #x00000010)))",
        x = x,
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
        format!("rev32ret_{id}", id = id),
        String::from("(_ BitVec 32)"),
    ));
    solver.additional_assumptions.push(format!("(= rev32ret_{id} (bvor (bvlshr (bvand x4_{id} #xaaaaaaaa) #x00000001) (bvshl (bvand x4_{id} #x55555555) #x00000001)))", id = id));

    let padding = solver.new_fresh_bits(solver.bitwidth - 32);
    format!(
        "(concat {padding} rev32ret_{id})",
        padding = padding,
        id = id
    )
}

pub fn rev16(solver: &mut SolverCtx, x: SExpr, id: u32) -> SExpr {
    let x = format!("((_ extract 15 0) {})", x);

    solver
        .additional_decls
        .push((format!("x1_{id}", id = id), String::from("(_ BitVec 16)")));
    solver.additional_assumptions.push(format!(
        "(= x1_{id} (bvor (bvlshr {x} #x0008) (bvshl {x} #x0008)))",
        x = x,
        id = id
    ));

    solver
        .additional_decls
        .push((format!("x2_{id}", id = id), String::from("(_ BitVec 16)")));
    solver.additional_assumptions.push(format!("(= x2_{id} (bvor (bvlshr (bvand x1_{id} #xf0f0) #x0004) (bvshl (bvand x1_{id} #x0f0f) #x0004)))", id = id));

    solver
        .additional_decls
        .push((format!("x3_{id}", id = id), String::from("(_ BitVec 16)")));
    solver.additional_assumptions.push(format!("(= x3_{id} (bvor (bvlshr (bvand x2_{id} #xcccc) #x0002) (bvshl (bvand x2_{id} #x3333) #x0002)))", id = id));

    solver.additional_decls.push((
        format!("rev16ret_{id}", id = id),
        String::from("(_ BitVec 16)"),
    ));
    solver.additional_assumptions.push(format!("(= rev16ret_{id} (bvor (bvlshr (bvand x3_{id} #xaaaa) #x0001) (bvshl (bvand x3_{id} #x5555) #x0001)))", id = id));

    let padding = solver.new_fresh_bits(solver.bitwidth - 16);
    format!(
        "(concat {padding} rev16ret_{id})",
        padding = padding,
        id = id
    )
}

pub fn rev8(solver: &mut SolverCtx, x: SExpr, id: u32) -> SExpr {
    let x = format!("((_ extract 7 0) {})", x);

    solver
        .additional_decls
        .push((format!("x1_{id}", id = id), String::from("(_ BitVec 8)")));
    solver.additional_assumptions.push(format!(
        "(= x1_{id} (bvor (bvlshr {x} #x04) (bvshl {x} #x04)))",
        id = id,
        x = x
    ));

    solver
        .additional_decls
        .push((format!("x2_{id}", id = id), String::from("(_ BitVec 8)")));
    solver.additional_assumptions.push(format!(
        "(= x2_{id} (bvor (bvlshr (bvand x1_{id} #xcc) #x02) (bvshl (bvand x1_{id} #x33) #x02)))",
        id = id
    ));

    solver.additional_decls.push((
        format!("rev8ret_{id}", id = id),
        String::from("(_ BitVec 8)"),
    ));
    solver.additional_assumptions.push(format!("(= rev8ret_{id} (bvor (bvlshr (bvand x2_{id} #xaa) #x01) (bvshl (bvand x2_{id} #x55) #x01)))", id = id));

    let padding = solver.new_fresh_bits(solver.bitwidth - 8);
    format!(
        "(concat {padding} rev8ret_{id})",
        padding = padding,
        id = id
    )
}
*/

pub fn rev1(solver: &mut SolverCtx, x: SExpr, id: u32) -> SExpr {
    let bv1 = solver.smt.bit_vec_sort(solver.smt.numeral(32));

    let extract = solver.smt.extract(0, 0, x);
    
    let rev1ret = solver.declare(format!("rev1ret_{id}", id = id), bv1);
    solver.assume(
        solver.smt.eq(rev1ret, extract)
    );

    let padding = solver.new_fresh_bits(solver.bitwidth - 1);
    solver.smt.concat(padding, rev1ret)
}

#[cfg(test)]
mod tests {
    use veri_ir::TypeContext;

    use crate::solver::SolverCtx;
    use std::collections::{HashMap, HashSet};

    #[test]
    fn rev1_test() {
        let mut smt = easy_smt::ContextBuilder::new().build().unwrap();

        // Seems like we could make it easier to construct a test context!
        let mut ctx = SolverCtx {
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
        };
        
        let x = ctx.smt.atom("x");
        let res = crate::solver::encoded_ops::rev::rev1(&mut ctx, x, 42);
        assert_eq!(format!("{}", ctx.smt.display(res)), "(concat fresh0 rev1ret_42)");
    }
}
