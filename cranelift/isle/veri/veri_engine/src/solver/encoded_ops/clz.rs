use crate::solver::SolverCtx;
use easy_smt::SExpr;

// Adapted from https://stackoverflow.com/questions/23856596/how-to-count-leading-zeros-in-a-32-bit-unsigned-integer

pub fn a64clz32(solver: &mut SolverCtx, x: SExpr, id: u32) -> SExpr {
    let bv32 = solver.smt.bit_vec_sort(solver.usize(32));
    let bv64 = solver.smt.bit_vec_sort(solver.usize(64));

    // extract to ensure we have a 32 bit input
    let a64x_name = format!("a64x_{id}", id = id);
    let a64x = solver.smt.atom(a64x_name);
    solver
        .additional_decls
        .push((a64x_name, bv32));
    solver.additional_assumptions.push(
       solver.smt.eq(a64x, solver.smt.extract(31, 0, x))
    );

    // total zeros counter
    let ret0_name = format!("ret0_{id}", id = id);
    let ret0 = solver.smt.atom(ret0);
    solver
        .additional_decls
        .push((ret0_name, bv64));
    solver
        .additional_assumptions
        .push(solver.smt.eq(solver.smt.atom(ret0), solver.bv(0, 64)));

    // round 1
    let ret1 = format!("ret1_{id}", id = id);
    solver.additional_decls.push((ret1, bv64));
    let y16 = format!("y16_{id}", id = id);
    solver.additional_decls.push((y16, bv32));
    let x16 = format!("x16_{id}", id = id);
    solver.additional_decls.push((x16, bv32));
    
    solver.additional_assumptions.push(solver.smt.eq(
        solver.smt.atom(y16),
        solver.smt.bvlshr(solver.smt.atom(a64x), solver.smt.atom("#x00000010")),
    ));
    solver.additional_assumptions.push(format!("(ite (not (= y16_{id} (_ bv0 32))) (= ret1_{id} ret0_{id}) (= ret1_{id} (bvadd ret0_{id} (_ bv16 64))))", id = id));
    solver.additional_assumptions.push(
        solver.smt.ite(
            solver.smt.not(solver.smt.eq(y16, solver.bv(0, 32))),
            solver.smt.eq(x16, y16),
            solver.smt.eq(x16, a64x),
        )
    );

    // round 2
    solver
        .additional_decls
        .push((format!("ret2_{id}", id = id), String::from("(_ BitVec 64)")));
    solver
        .additional_decls
        .push((format!("y8_{id}", id = id), String::from("(_ BitVec 32)")));
    solver
        .additional_decls
        .push((format!("x8_{id}", id = id), String::from("(_ BitVec 32)")));

    solver
        .additional_assumptions
        .push(format!("(= y8_{id} (bvlshr x16_{id} #x00000008))", id = id));
    solver.additional_assumptions.push(format!("(ite (not (= y8_{id} (_ bv0 32))) (= ret2_{id} ret1_{id}) (= ret2_{id} (bvadd ret1_{id} (_ bv8 64))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= y8_{id} (_ bv0 32))) (= x8_{id} y8_{id}) (= x8_{id} x16_{id}))",
        id = id
    ));

    // round 3
    solver
        .additional_decls
        .push((format!("ret3_{id}", id = id), String::from("(_ BitVec 64)")));
    solver
        .additional_decls
        .push((format!("y4_{id}", id = id), String::from("(_ BitVec 32)")));
    solver
        .additional_decls
        .push((format!("x4_{id}", id = id), String::from("(_ BitVec 32)")));

    solver
        .additional_assumptions
        .push(format!("(= y4_{id} (bvlshr x8_{id} #x00000004))", id = id));
    solver.additional_assumptions.push(format!("(ite (not (= y4_{id} (_ bv0 32))) (= ret3_{id} ret2_{id}) (= ret3_{id} (bvadd ret2_{id} (_ bv4 64))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= y4_{id} (_ bv0 32))) (= x4_{id} y4_{id}) (= x4_{id} x8_{id}))",
        id = id
    ));

    // round 4
    solver
        .additional_decls
        .push((format!("ret4_{id}", id = id), String::from("(_ BitVec 64)")));
    solver
        .additional_decls
        .push((format!("y2_{id}", id = id), String::from("(_ BitVec 32)")));
    solver
        .additional_decls
        .push((format!("x2_{id}", id = id), String::from("(_ BitVec 32)")));

    solver
        .additional_assumptions
        .push(format!("(= y2_{id} (bvlshr x4_{id} #x00000002))", id = id));
    solver.additional_assumptions.push(format!("(ite (not (= y2_{id} (_ bv0 32))) (= ret4_{id} ret3_{id}) (= ret4_{id} (bvadd ret3_{id} (_ bv2 64))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= y2_{id} (_ bv0 32))) (= x2_{id} y2_{id}) (= x2_{id} x4_{id}))",
        id = id
    ));

    // round 5
    solver
        .additional_decls
        .push((format!("ret5_{id}", id = id), String::from("(_ BitVec 64)")));
    solver
        .additional_decls
        .push((format!("y1_{id}", id = id), String::from("(_ BitVec 32)")));
    solver
        .additional_decls
        .push((format!("x1_{id}", id = id), String::from("(_ BitVec 32)")));

    solver
        .additional_assumptions
        .push(format!("(= y1_{id} (bvlshr x2_{id} #x00000001))", id = id));
    solver.additional_assumptions.push(format!("(ite (not (= y1_{id} (_ bv0 32))) (= ret5_{id} ret4_{id}) (= ret5_{id} (bvadd ret4_{id} (_ bv1 64))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= y1_{id} (_ bv0 32))) (= x1_{id} y1_{id}) (= x1_{id} x2_{id}))",
        id = id
    ));

    // last round
    solver
        .additional_decls
        .push((format!("ret6_{id}", id = id), String::from("(_ BitVec 64)")));
    solver.additional_assumptions.push(format!("(ite (not (= x1_{id} (_ bv0 32))) (= ret6_{id} ret5_{id}) (= ret6_{id} (bvadd ret5_{id} (_ bv1 64))))", id = id));

    // final return
    format!("ret6_{id}", id = id)
}

pub fn clz64(solver: &mut SolverCtx, x: SExpr, id: u32) -> SExpr {
    // total zeros counter
    solver
        .additional_decls
        .push((format!("ret0_{id}", id = id), String::from("(_ BitVec 64)")));
    solver
        .additional_assumptions
        .push(format!("(= ret0_{id} (_ bv0 64))", id = id));

    // round 1
    solver
        .additional_decls
        .push((format!("ret1_{id}", id = id), String::from("(_ BitVec 64)")));
    solver
        .additional_decls
        .push((format!("y32_{id}", id = id), String::from("(_ BitVec 64)")));
    solver
        .additional_decls
        .push((format!("x32_{id}", id = id), String::from("(_ BitVec 64)")));

    solver.additional_assumptions.push(format!(
        "(= y32_{id} (bvlshr {x} #x0000000000000020))",
        x = x,
        id = id
    ));
    solver.additional_assumptions.push(format!("(ite (not (= y32_{id} (_ bv0 64))) (= ret1_{id} ret0_{id}) (= ret1_{id} (bvadd ret0_{id} (_ bv32 64))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= y32_{id} (_ bv0 64))) (= x32_{id} y32_{id}) (= x32_{id} {x}))",
        x = x,
        id = id
    ));

    // round 2
    solver
        .additional_decls
        .push((format!("ret2_{id}", id = id), String::from("(_ BitVec 64)")));
    solver
        .additional_decls
        .push((format!("y16_{id}", id = id), String::from("(_ BitVec 64)")));
    solver
        .additional_decls
        .push((format!("x16_{id}", id = id), String::from("(_ BitVec 64)")));

    solver.additional_assumptions.push(format!(
        "(= y16_{id} (bvlshr x32_{id} #x0000000000000010))",
        id = id
    ));
    solver.additional_assumptions.push(format!("(ite (not (= y16_{id} (_ bv0 64))) (= ret2_{id} ret1_{id}) (= ret2_{id} (bvadd ret1_{id} (_ bv16 64))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= y16_{id} (_ bv0 64))) (= x16_{id} y16_{id}) (= x16_{id} x32_{id}))",
        id = id
    ));

    // round 3
    solver
        .additional_decls
        .push((format!("ret3_{id}", id = id), String::from("(_ BitVec 64)")));
    solver
        .additional_decls
        .push((format!("y8_{id}", id = id), String::from("(_ BitVec 64)")));
    solver
        .additional_decls
        .push((format!("x8_{id}", id = id), String::from("(_ BitVec 64)")));

    solver.additional_assumptions.push(format!(
        "(= y8_{id} (bvlshr x16_{id} #x0000000000000008))",
        id = id
    ));
    solver.additional_assumptions.push(format!("(ite (not (= y8_{id} (_ bv0 64))) (= ret3_{id} ret2_{id}) (= ret3_{id} (bvadd ret2_{id} (_ bv8 64))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= y8_{id} (_ bv0 64))) (= x8_{id} y8_{id}) (= x8_{id} x16_{id}))",
        id = id
    ));

    // round 4
    solver
        .additional_decls
        .push((format!("ret4_{id}", id = id), String::from("(_ BitVec 64)")));
    solver
        .additional_decls
        .push((format!("y4_{id}", id = id), String::from("(_ BitVec 64)")));
    solver
        .additional_decls
        .push((format!("x4_{id}", id = id), String::from("(_ BitVec 64)")));

    solver.additional_assumptions.push(format!(
        "(= y4_{id} (bvlshr x8_{id} #x0000000000000004))",
        id = id
    ));
    solver.additional_assumptions.push(format!("(ite (not (= y4_{id} (_ bv0 64))) (= ret4_{id} ret3_{id}) (= ret4_{id} (bvadd ret3_{id} (_ bv4 64))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= y4_{id} (_ bv0 64))) (= x4_{id} y4_{id}) (= x4_{id} x8_{id}))",
        id = id
    ));

    // round 5
    solver
        .additional_decls
        .push((format!("ret5_{id}", id = id), String::from("(_ BitVec 64)")));
    solver
        .additional_decls
        .push((format!("y2_{id}", id = id), String::from("(_ BitVec 64)")));
    solver
        .additional_decls
        .push((format!("x2_{id}", id = id), String::from("(_ BitVec 64)")));

    solver.additional_assumptions.push(format!(
        "(= y2_{id} (bvlshr x4_{id} #x0000000000000002))",
        id = id
    ));
    solver.additional_assumptions.push(format!("(ite (not (= y2_{id} (_ bv0 64))) (= ret5_{id} ret4_{id}) (= ret5_{id} (bvadd ret4_{id} (_ bv2 64))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= y2_{id} (_ bv0 64))) (= x2_{id} y2_{id}) (= x2_{id} x4_{id}))",
        id = id
    ));

    // round 6
    solver
        .additional_decls
        .push((format!("ret6_{id}", id = id), String::from("(_ BitVec 64)")));
    solver
        .additional_decls
        .push((format!("y1_{id}", id = id), String::from("(_ BitVec 64)")));
    solver
        .additional_decls
        .push((format!("x1_{id}", id = id), String::from("(_ BitVec 64)")));

    solver.additional_assumptions.push(format!(
        "(= y1_{id} (bvlshr x2_{id} #x0000000000000001))",
        id = id
    ));
    solver.additional_assumptions.push(format!("(ite (not (= y1_{id} (_ bv0 64))) (= ret6_{id} ret5_{id}) (= ret6_{id} (bvadd ret5_{id} (_ bv1 64))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= y1_{id} (_ bv0 64))) (= x1_{id} y1_{id}) (= x1_{id} x2_{id}))",
        id = id
    ));

    // last round
    solver
        .additional_decls
        .push((format!("ret7_{id}", id = id), String::from("(_ BitVec 64)")));
    solver.additional_assumptions.push(format!("(ite (not (= x1_{id} (_ bv0 64))) (= ret7_{id} ret6_{id}) (= ret7_{id} (bvadd ret6_{id} (_ bv1 64))))", id = id));

    // final return
    format!("ret7_{id}", id = id)
}

pub fn clz32(solver: &mut SolverCtx, x: SExpr, id: u32) -> SExpr {
    let x = format!("((_ extract 31 0) {})", x);

    // total zeros counter
    solver
        .additional_decls
        .push((format!("ret0_{id}", id = id), String::from("(_ BitVec 32)")));
    solver
        .additional_assumptions
        .push(format!("(= ret0_{id} (_ bv0 32))", id = id));

    // round 1
    solver
        .additional_decls
        .push((format!("ret1_{id}", id = id), String::from("(_ BitVec 32)")));
    solver
        .additional_decls
        .push((format!("y16_{id}", id = id), String::from("(_ BitVec 32)")));
    solver
        .additional_decls
        .push((format!("x16_{id}", id = id), String::from("(_ BitVec 32)")));

    solver.additional_assumptions.push(format!(
        "(= y16_{id} (bvlshr {x} #x00000010))",
        x = x,
        id = id
    ));
    solver.additional_assumptions.push(format!("(ite (not (= y16_{id} (_ bv0 32))) (= ret1_{id} ret0_{id}) (= ret1_{id} (bvadd ret0_{id} (_ bv16 32))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= y16_{id} (_ bv0 32))) (= x16_{id} y16_{id}) (= x16_{id} {x}))",
        x = x,
        id = id
    ));

    // round 2
    solver
        .additional_decls
        .push((format!("ret2_{id}", id = id), String::from("(_ BitVec 32)")));
    solver
        .additional_decls
        .push((format!("y8_{id}", id = id), String::from("(_ BitVec 32)")));
    solver
        .additional_decls
        .push((format!("x8_{id}", id = id), String::from("(_ BitVec 32)")));

    solver
        .additional_assumptions
        .push(format!("(= y8_{id} (bvlshr x16_{id} #x00000008))", id = id));
    solver.additional_assumptions.push(format!("(ite (not (= y8_{id} (_ bv0 32))) (= ret2_{id} ret1_{id}) (= ret2_{id} (bvadd ret1_{id} (_ bv8 32))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= y8_{id} (_ bv0 32))) (= x8_{id} y8_{id}) (= x8_{id} x16_{id}))",
        id = id
    ));

    // round 3
    solver
        .additional_decls
        .push((format!("ret3_{id}", id = id), String::from("(_ BitVec 32)")));
    solver
        .additional_decls
        .push((format!("y4_{id}", id = id), String::from("(_ BitVec 32)")));
    solver
        .additional_decls
        .push((format!("x4_{id}", id = id), String::from("(_ BitVec 32)")));

    solver
        .additional_assumptions
        .push(format!("(= y4_{id} (bvlshr x8_{id} #x00000004))", id = id));
    solver.additional_assumptions.push(format!("(ite (not (= y4_{id} (_ bv0 32))) (= ret3_{id} ret2_{id}) (= ret3_{id} (bvadd ret2_{id} (_ bv4 32))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= y4_{id} (_ bv0 32))) (= x4_{id} y4_{id}) (= x4_{id} x8_{id}))",
        id = id
    ));

    // round 4
    solver
        .additional_decls
        .push((format!("ret4_{id}", id = id), String::from("(_ BitVec 32)")));
    solver
        .additional_decls
        .push((format!("y2_{id}", id = id), String::from("(_ BitVec 32)")));
    solver
        .additional_decls
        .push((format!("x2_{id}", id = id), String::from("(_ BitVec 32)")));

    solver
        .additional_assumptions
        .push(format!("(= y2_{id} (bvlshr x4_{id} #x00000002))", id = id));
    solver.additional_assumptions.push(format!("(ite (not (= y2_{id} (_ bv0 32))) (= ret4_{id} ret3_{id}) (= ret4_{id} (bvadd ret3_{id} (_ bv2 32))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= y2_{id} (_ bv0 32))) (= x2_{id} y2_{id}) (= x2_{id} x4_{id}))",
        id = id
    ));

    // round 5
    solver
        .additional_decls
        .push((format!("ret5_{id}", id = id), String::from("(_ BitVec 32)")));
    solver
        .additional_decls
        .push((format!("y1_{id}", id = id), String::from("(_ BitVec 32)")));
    solver
        .additional_decls
        .push((format!("x1_{id}", id = id), String::from("(_ BitVec 32)")));

    solver
        .additional_assumptions
        .push(format!("(= y1_{id} (bvlshr x2_{id} #x00000001))", id = id));
    solver.additional_assumptions.push(format!("(ite (not (= y1_{id} (_ bv0 32))) (= ret5_{id} ret4_{id}) (= ret5_{id} (bvadd ret4_{id} (_ bv1 32))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= y1_{id} (_ bv0 32))) (= x1_{id} y1_{id}) (= x1_{id} x2_{id}))",
        id = id
    ));

    // last round
    solver
        .additional_decls
        .push((format!("ret6_{id}", id = id), String::from("(_ BitVec 32)")));
    solver.additional_assumptions.push(format!("(ite (not (= x1_{id} (_ bv0 32))) (= ret6_{id} ret5_{id}) (= ret6_{id} (bvadd ret5_{id} (_ bv1 32))))", id = id));

    // final return
    let padding = solver.new_fresh_bits(solver.bitwidth - 32);
    format!("(concat {padding} ret6_{id})", padding = padding, id = id)
}

pub fn clz16(solver: &mut SolverCtx, x: SExpr, id: u32) -> SExpr {
    let x = format!("((_ extract 15 0) {})", x);

    // total zeros counter
    solver
        .additional_decls
        .push((format!("ret1_{id}", id = id), String::from("(_ BitVec 16)")));
    solver
        .additional_assumptions
        .push(format!("(= ret1_{id} (_ bv0 16))", id = id));

    // round 1
    solver
        .additional_decls
        .push((format!("ret2_{id}", id = id), String::from("(_ BitVec 16)")));
    solver
        .additional_decls
        .push((format!("y8_{id}", id = id), String::from("(_ BitVec 16)")));
    solver
        .additional_decls
        .push((format!("x8_{id}", id = id), String::from("(_ BitVec 16)")));

    solver
        .additional_assumptions
        .push(format!("(= y8_{id} (bvlshr {x} #x0008))", x = x, id = id));
    solver.additional_assumptions.push(format!("(ite (not (= y8_{id} (_ bv0 16))) (= ret2_{id} ret1_{id}) (= ret2_{id} (bvadd ret1_{id} (_ bv8 16))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= y8_{id} (_ bv0 16))) (= x8_{id} y8_{id}) (= x8_{id} {x}))",
        x = x,
        id = id
    ));

    // round 2
    solver
        .additional_decls
        .push((format!("ret3_{id}", id = id), String::from("(_ BitVec 16)")));
    solver
        .additional_decls
        .push((format!("y4_{id}", id = id), String::from("(_ BitVec 16)")));
    solver
        .additional_decls
        .push((format!("x4_{id}", id = id), String::from("(_ BitVec 16)")));

    solver
        .additional_assumptions
        .push(format!("(= y4_{id} (bvlshr x8_{id} #x0004))", id = id));
    solver.additional_assumptions.push(format!("(ite (not (= y4_{id} (_ bv0 16))) (= ret3_{id} ret2_{id}) (= ret3_{id} (bvadd ret2_{id} (_ bv4 16))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= y4_{id} (_ bv0 16))) (= x4_{id} y4_{id}) (= x4_{id} x8_{id}))",
        id = id
    ));

    // round 3
    solver
        .additional_decls
        .push((format!("ret4_{id}", id = id), String::from("(_ BitVec 16)")));
    solver
        .additional_decls
        .push((format!("y2_{id}", id = id), String::from("(_ BitVec 16)")));
    solver
        .additional_decls
        .push((format!("x2_{id}", id = id), String::from("(_ BitVec 16)")));

    solver
        .additional_assumptions
        .push(format!("(= y2_{id} (bvlshr x4_{id} #x0002))", id = id));
    solver.additional_assumptions.push(format!("(ite (not (= y2_{id} (_ bv0 16))) (= ret4_{id} ret3_{id}) (= ret4_{id} (bvadd ret3_{id} (_ bv2 16))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= y2_{id} (_ bv0 16))) (= x2_{id} y2_{id}) (= x2_{id} x4_{id}))",
        id = id
    ));

    // round 4
    solver
        .additional_decls
        .push((format!("ret5_{id}", id = id), String::from("(_ BitVec 16)")));
    solver
        .additional_decls
        .push((format!("y1_{id}", id = id), String::from("(_ BitVec 16)")));
    solver
        .additional_decls
        .push((format!("x1_{id}", id = id), String::from("(_ BitVec 16)")));

    solver
        .additional_assumptions
        .push(format!("(= y1_{id} (bvlshr x2_{id} #x0001))", id = id));
    solver.additional_assumptions.push(format!("(ite (not (= y1_{id} (_ bv0 16))) (= ret5_{id} ret4_{id}) (= ret5_{id} (bvadd ret4_{id} (_ bv1 16))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= y1_{id} (_ bv0 16))) (= x1_{id} y1_{id}) (= x1_{id} x2_{id}))",
        id = id
    ));

    // last round
    solver
        .additional_decls
        .push((format!("ret6_{id}", id = id), String::from("(_ BitVec 16)")));
    solver.additional_assumptions.push(format!("(ite (not (= x1_{id} (_ bv0 16))) (= ret6_{id} ret5_{id}) (= ret6_{id} (bvadd ret5_{id} (_ bv1 16))))", id = id));

    // final return
    let padding = solver.new_fresh_bits(solver.bitwidth - 16);
    format!("(concat {padding} ret6_{id})", padding = padding, id = id)
}

pub fn clz8(solver: &mut SolverCtx, x: SExpr, id: u32) -> SExpr {
    let x = format!("((_ extract 7 0) {})", x);

    // total zeros counter
    solver
        .additional_decls
        .push((format!("ret0_{id}", id = id), String::from("(_ BitVec 8)")));
    solver
        .additional_assumptions
        .push(format!("(= ret0_{id} (_ bv0 8))", id = id));

    // round 1
    solver
        .additional_decls
        .push((format!("ret3_{id}", id = id), String::from("(_ BitVec 8)")));
    solver
        .additional_decls
        .push((format!("y4_{id}", id = id), String::from("(_ BitVec 8)")));
    solver
        .additional_decls
        .push((format!("x4_{id}", id = id), String::from("(_ BitVec 8)")));

    solver
        .additional_assumptions
        .push(format!("(= y4_{id} (bvlshr {x} #x04))", x = x, id = id));
    solver.additional_assumptions.push(format!("(ite (not (= y4_{id} (_ bv0 8))) (= ret3_{id} ret0_{id}) (= ret3_{id} (bvadd ret0_{id} (_ bv4 8))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= y4_{id} (_ bv0 8))) (= x4_{id} y4_{id}) (= x4_{id} {x}))",
        x = x,
        id = id
    ));

    // round 2
    solver
        .additional_decls
        .push((format!("ret4_{id}", id = id), String::from("(_ BitVec 8)")));
    solver
        .additional_decls
        .push((format!("y2_{id}", id = id), String::from("(_ BitVec 8)")));
    solver
        .additional_decls
        .push((format!("x2_{id}", id = id), String::from("(_ BitVec 8)")));

    solver
        .additional_assumptions
        .push(format!("(= y2_{id} (bvlshr x4_{id} #x02))", id = id));
    solver.additional_assumptions.push(format!("(ite (not (= y2_{id} (_ bv0 8))) (= ret4_{id} ret3_{id}) (= ret4_{id} (bvadd ret3_{id} (_ bv2 8))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= y2_{id} (_ bv0 8))) (= x2_{id} y2_{id}) (= x2_{id} x4_{id}))",
        id = id
    ));

    // round 3
    solver
        .additional_decls
        .push((format!("ret5_{id}", id = id), String::from("(_ BitVec 8)")));
    solver
        .additional_decls
        .push((format!("y1_{id}", id = id), String::from("(_ BitVec 8)")));
    solver
        .additional_decls
        .push((format!("x1_{id}", id = id), String::from("(_ BitVec 8)")));

    solver
        .additional_assumptions
        .push(format!("(= y1_{id} (bvlshr x2_{id} #x01))", id = id));
    solver.additional_assumptions.push(format!("(ite (not (= y1_{id} (_ bv0 8))) (= ret5_{id} ret4_{id}) (= ret5_{id} (bvadd ret4_{id} (_ bv1 8))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= y1_{id} (_ bv0 8))) (= x1_{id} y1_{id}) (= x1_{id} x2_{id}))",
        id = id
    ));

    // last round
    solver
        .additional_decls
        .push((format!("ret6_{id}", id = id), String::from("(_ BitVec 8)")));
    solver.additional_assumptions.push(format!("(ite (not (= x1_{id} (_ bv0 8))) (= ret6_{id} ret5_{id}) (= ret6_{id} (bvadd ret5_{id} (_ bv1 8))))", id = id));

    // final return
    let padding = solver.new_fresh_bits(solver.bitwidth - 8);
    format!("(concat {padding} ret6_{id})", padding = padding, id = id)
}

pub fn clz1(solver: &mut SolverCtx, x: SExpr, id: u32) -> SExpr {
    let extract = format!("((_ extract 0 0) {})", x);
    solver
        .additional_decls
        .push((format!("ret_{id}", id = id), String::from("(_ BitVec 1)")));
    solver
        .additional_assumptions
        .push(format!("(= ret_{id} (bvnot {x}))", id = id, x = extract));

    let padding = solver.new_fresh_bits(solver.bitwidth - 1);
    format!("(concat {padding} ret_{id})", padding = padding, id = id)
}
