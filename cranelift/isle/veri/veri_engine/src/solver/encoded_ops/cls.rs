use crate::solver::SolverCtx;
use easy_smt::SExpr;

// Adapted from https://stackoverflow.com/questions/23856596/how-to-count-leading-zeros-in-a-32-bit-unsigned-integer

pub fn a64cls32(solver: &mut SolverCtx, x: SExpr, id: u32) -> SExpr {
    // extract to ensure we have a 32 bit input
    solver
        .additional_decls
        .push((format!("a64x_{id}", id = id), String::from("(_ BitVec 32)")));
    solver.additional_assumptions.push(format!(
        "(= a64x_{id} ((_ extract 31 0) {x}))",
        id = id,
        x = x
    ));

    // total zeros counter
    solver.additional_decls.push((
        format!("zret0_{id}", id = id),
        String::from("(_ BitVec 64)"),
    ));
    solver
        .additional_assumptions
        .push(format!("(= zret0_{id} (_ bv0 64))", id = id));

    // round 1
    solver.additional_decls.push((
        format!("zret2_{id}", id = id),
        String::from("(_ BitVec 64)"),
    ));
    solver
        .additional_decls
        .push((format!("zy16_{id}", id = id), String::from("(_ BitVec 32)")));
    solver
        .additional_decls
        .push((format!("zx16_{id}", id = id), String::from("(_ BitVec 32)")));

    solver.additional_assumptions.push(format!(
        "(= zy16_{id} (bvlshr a64x_{id} #x00000010))",
        id = id
    ));
    solver.additional_assumptions.push(format!("(ite (not (= zy16_{id} (_ bv0 32))) (= zret2_{id} zret0_{id}) (= zret2_{id} (bvadd zret0_{id} (_ bv16 64))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= zy16_{id} (_ bv0 32))) (= zx16_{id} zy16_{id}) (= zx16_{id} a64x_{id}))",
        id = id
    ));

    // round 2
    solver.additional_decls.push((
        format!("zret3_{id}", id = id),
        String::from("(_ BitVec 64)"),
    ));
    solver
        .additional_decls
        .push((format!("zy8_{id}", id = id), String::from("(_ BitVec 32)")));
    solver
        .additional_decls
        .push((format!("zx8_{id}", id = id), String::from("(_ BitVec 32)")));

    solver.additional_assumptions.push(format!(
        "(= zy8_{id} (bvlshr zx16_{id} #x00000008))",
        id = id
    ));
    solver.additional_assumptions.push(format!("(ite (not (= zy8_{id} (_ bv0 32))) (= zret3_{id} zret2_{id}) (= zret3_{id} (bvadd zret2_{id} (_ bv8 64))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= zy8_{id} (_ bv0 32))) (= zx8_{id} zy8_{id}) (= zx8_{id} zx16_{id}))",
        id = id
    ));

    // round 3
    solver.additional_decls.push((
        format!("zret4_{id}", id = id),
        String::from("(_ BitVec 64)"),
    ));
    solver
        .additional_decls
        .push((format!("zy4_{id}", id = id), String::from("(_ BitVec 32)")));
    solver
        .additional_decls
        .push((format!("zx4_{id}", id = id), String::from("(_ BitVec 32)")));

    solver.additional_assumptions.push(format!(
        "(= zy4_{id} (bvlshr zx8_{id} #x00000004))",
        id = id
    ));
    solver.additional_assumptions.push(format!("(ite (not (= zy4_{id} (_ bv0 32))) (= zret4_{id} zret3_{id}) (= zret4_{id} (bvadd zret3_{id} (_ bv4 64))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= zy4_{id} (_ bv0 32))) (= zx4_{id} zy4_{id}) (= zx4_{id} zx8_{id}))",
        id = id
    ));

    // round 4
    solver.additional_decls.push((
        format!("zret5_{id}", id = id),
        String::from("(_ BitVec 64)"),
    ));
    solver
        .additional_decls
        .push((format!("zy2_{id}", id = id), String::from("(_ BitVec 32)")));
    solver
        .additional_decls
        .push((format!("zx2_{id}", id = id), String::from("(_ BitVec 32)")));

    solver.additional_assumptions.push(format!(
        "(= zy2_{id} (bvlshr zx4_{id} #x00000002))",
        id = id
    ));
    solver.additional_assumptions.push(format!("(ite (not (= zy2_{id} (_ bv0 32))) (= zret5_{id} zret4_{id}) (= zret5_{id} (bvadd zret4_{id} (_ bv2 64))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= zy2_{id} (_ bv0 32))) (= zx2_{id} zy2_{id}) (= zx2_{id} zx4_{id}))",
        id = id
    ));

    // round 5
    solver.additional_decls.push((
        format!("zret6_{id}", id = id),
        String::from("(_ BitVec 64)"),
    ));
    solver
        .additional_decls
        .push((format!("zy1_{id}", id = id), String::from("(_ BitVec 32)")));
    solver
        .additional_decls
        .push((format!("zx1_{id}", id = id), String::from("(_ BitVec 32)")));

    solver.additional_assumptions.push(format!(
        "(= zy1_{id} (bvlshr zx2_{id} #x00000001))",
        id = id
    ));
    solver.additional_assumptions.push(format!("(ite (not (= zy1_{id} (_ bv0 32))) (= zret6_{id} zret5_{id}) (= zret6_{id} (bvadd zret5_{id} (_ bv1 64))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= zy1_{id} (_ bv0 32))) (= zx1_{id} zy1_{id}) (= zx1_{id} zx2_{id}))",
        id = id
    ));

    // last round
    solver.additional_decls.push((
        format!("zret7_{id}", id = id),
        String::from("(_ BitVec 64)"),
    ));
    solver.additional_assumptions.push(format!("(ite (not (= zx1_{id} (_ bv0 32))) (= zret7_{id} zret6_{id}) (= zret7_{id} (bvadd zret6_{id} (_ bv1 64))))", id = id));

    solver.additional_decls.push((
        format!("clzret_{id}", id = id),
        String::from("(_ BitVec 64)"),
    ));
    solver.additional_assumptions.push(format!("(ite (= zret7_{id} (_ bv0 64)) (= clzret_{id} zret7_{id}) (= clzret_{id} (bvsub zret7_{id} (_ bv1 64))))", id = id));

    // total zeros counter
    solver.additional_decls.push((
        format!("sret0_{id}", id = id),
        String::from("(_ BitVec 64)"),
    ));
    solver
        .additional_assumptions
        .push(format!("(= sret0_{id} (_ bv0 64))", id = id));

    // round 1
    solver.additional_decls.push((
        format!("sret2_{id}", id = id),
        String::from("(_ BitVec 64)"),
    ));
    solver
        .additional_decls
        .push((format!("sy16_{id}", id = id), String::from("(_ BitVec 32)")));
    solver
        .additional_decls
        .push((format!("sx16_{id}", id = id), String::from("(_ BitVec 32)")));

    solver.additional_assumptions.push(format!(
        "(= sy16_{id} (bvashr a64x_{id} #x00000010))",
        id = id
    ));
    solver.additional_assumptions.push(format!("(ite (not (= sy16_{id} (_ bv4294967295 32))) (= sret2_{id} sret0_{id}) (= sret2_{id} (bvadd sret0_{id} (_ bv16 64))))", id = id));
    solver.additional_assumptions.push(format!("(ite (not (= sy16_{id} (_ bv4294967295 32))) (= sx16_{id} sy16_{id}) (= sx16_{id} a64x_{id}))", id = id));

    // round 2
    solver.additional_decls.push((
        format!("sret3_{id}", id = id),
        String::from("(_ BitVec 64)"),
    ));
    solver
        .additional_decls
        .push((format!("sy8_{id}", id = id), String::from("(_ BitVec 32)")));
    solver
        .additional_decls
        .push((format!("sx8_{id}", id = id), String::from("(_ BitVec 32)")));

    solver.additional_assumptions.push(format!(
        "(= sy8_{id} (bvashr sx16_{id} #x00000008))",
        id = id
    ));
    solver.additional_assumptions.push(format!("(ite (not (= sy8_{id} (_ bv4294967295 32))) (= sret3_{id} sret2_{id}) (= sret3_{id} (bvadd sret2_{id} (_ bv8 64))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= sy8_{id} (_ bv4294967295 32))) (= sx8_{id} sy8_{id}) (= sx8_{id} sx16_{id}))",
        id = id
    ));

    // round 3
    solver.additional_decls.push((
        format!("sret4_{id}", id = id),
        String::from("(_ BitVec 64)"),
    ));
    solver
        .additional_decls
        .push((format!("sy4_{id}", id = id), String::from("(_ BitVec 32)")));
    solver
        .additional_decls
        .push((format!("sx4_{id}", id = id), String::from("(_ BitVec 32)")));

    solver.additional_assumptions.push(format!(
        "(= sy4_{id} (bvashr sx8_{id} #x00000004))",
        id = id
    ));
    solver.additional_assumptions.push(format!("(ite (not (= sy4_{id} (_ bv4294967295 32))) (= sret4_{id} sret3_{id}) (= sret4_{id} (bvadd sret3_{id} (_ bv4 64))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= sy4_{id} (_ bv4294967295 32))) (= sx4_{id} sy4_{id}) (= sx4_{id} sx8_{id}))",
        id = id
    ));

    // round 4
    solver.additional_decls.push((
        format!("sret5_{id}", id = id),
        String::from("(_ BitVec 64)"),
    ));
    solver
        .additional_decls
        .push((format!("sy2_{id}", id = id), String::from("(_ BitVec 32)")));
    solver
        .additional_decls
        .push((format!("sx2_{id}", id = id), String::from("(_ BitVec 32)")));

    solver.additional_assumptions.push(format!(
        "(= sy2_{id} (bvashr sx4_{id} #x00000002))",
        id = id
    ));
    solver.additional_assumptions.push(format!("(ite (not (= sy2_{id} (_ bv4294967295 32))) (= sret5_{id} sret4_{id}) (= sret5_{id} (bvadd sret4_{id} (_ bv2 64))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= sy2_{id} (_ bv4294967295 32))) (= sx2_{id} sy2_{id}) (= sx2_{id} sx4_{id}))",
        id = id
    ));

    // round 5
    solver.additional_decls.push((
        format!("sret6_{id}", id = id),
        String::from("(_ BitVec 64)"),
    ));
    solver
        .additional_decls
        .push((format!("sy1_{id}", id = id), String::from("(_ BitVec 32)")));
    solver
        .additional_decls
        .push((format!("sx1_{id}", id = id), String::from("(_ BitVec 32)")));

    solver.additional_assumptions.push(format!(
        "(= sy1_{id} (bvashr sx2_{id} #x00000001))",
        id = id
    ));
    solver.additional_assumptions.push(format!("(ite (not (= sy1_{id} (_ bv4294967295 32))) (= sret6_{id} sret5_{id}) (= sret6_{id} (bvadd sret5_{id} (_ bv1 64))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= sy1_{id} (_ bv4294967295 32))) (= sx1_{id} sy1_{id}) (= sx1_{id} sx2_{id}))",
        id = id
    ));

    // last round
    solver.additional_decls.push((
        format!("sret7_{id}", id = id),
        String::from("(_ BitVec 64)"),
    ));
    solver.additional_assumptions.push(format!("(ite (not (= sx1_{id} (_ bv4294967295 32))) (= sret7_{id} sret6_{id}) (= sret7_{id} (bvadd sret6_{id} (_ bv1 64))))", id = id));

    solver.additional_decls.push((
        format!("clsret_{id}", id = id),
        String::from("(_ BitVec 64)"),
    ));
    solver.additional_assumptions.push(format!("(ite (= sret7_{id} (_ bv0 64)) (= clsret_{id} sret7_{id}) (= clsret_{id} (bvsub sret7_{id} (_ bv1 64))))", id = id));

    // final return
    solver.additional_decls.push((
        format!("a64cls32ret_{id}", id = id),
        String::from("(_ BitVec 64)"),
    ));
    solver.additional_assumptions.push(format!("(ite (bvsle (_ bv0 32) a64x_{id}) (= a64cls32ret_{id} clzret_{id}) (= a64cls32ret_{id} clsret_{id}))", id = id));

    format!("a64cls32ret_{id}", id = id)
}

pub fn cls64(solver: &mut SolverCtx, x: SExpr, id: u32) -> SExpr {
    // total zeros counter
    solver.additional_decls.push((
        format!("zret0_{id}", id = id),
        String::from("(_ BitVec 64)"),
    ));
    solver
        .additional_assumptions
        .push(format!("(= zret0_{id} (_ bv0 64))", id = id));

    // round 1
    solver.additional_decls.push((
        format!("zret1_{id}", id = id),
        String::from("(_ BitVec 64)"),
    ));
    solver
        .additional_decls
        .push((format!("zy32_{id}", id = id), String::from("(_ BitVec 64)")));
    solver
        .additional_decls
        .push((format!("zx32_{id}", id = id), String::from("(_ BitVec 64)")));

    solver.additional_assumptions.push(format!(
        "(= zy32_{id} (bvlshr {x} #x0000000000000020))",
        x = x,
        id = id
    ));
    solver.additional_assumptions.push(format!("(ite (not (= zy32_{id} (_ bv0 64))) (= zret1_{id} zret0_{id}) (= zret1_{id} (bvadd zret0_{id} (_ bv32 64))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= zy32_{id} (_ bv0 64))) (= zx32_{id} zy32_{id}) (= zx32_{id} {x}))",
        x = x,
        id = id
    ));

    // round 2
    solver.additional_decls.push((
        format!("zret2_{id}", id = id),
        String::from("(_ BitVec 64)"),
    ));
    solver
        .additional_decls
        .push((format!("zy16_{id}", id = id), String::from("(_ BitVec 64)")));
    solver
        .additional_decls
        .push((format!("zx16_{id}", id = id), String::from("(_ BitVec 64)")));

    solver.additional_assumptions.push(format!(
        "(= zy16_{id} (bvlshr zx32_{id} #x0000000000000010))",
        id = id
    ));
    solver.additional_assumptions.push(format!("(ite (not (= zy16_{id} (_ bv0 64))) (= zret2_{id} zret1_{id}) (= zret2_{id} (bvadd zret1_{id} (_ bv16 64))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= zy16_{id} (_ bv0 64))) (= zx16_{id} zy16_{id}) (= zx16_{id} zx32_{id}))",
        id = id
    ));

    // round 3
    solver.additional_decls.push((
        format!("zret3_{id}", id = id),
        String::from("(_ BitVec 64)"),
    ));
    solver
        .additional_decls
        .push((format!("zy8_{id}", id = id), String::from("(_ BitVec 64)")));
    solver
        .additional_decls
        .push((format!("zx8_{id}", id = id), String::from("(_ BitVec 64)")));

    solver.additional_assumptions.push(format!(
        "(= zy8_{id} (bvlshr zx16_{id} #x0000000000000008))",
        id = id
    ));
    solver.additional_assumptions.push(format!("(ite (not (= zy8_{id} (_ bv0 64))) (= zret3_{id} zret2_{id}) (= zret3_{id} (bvadd zret2_{id} (_ bv8 64))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= zy8_{id} (_ bv0 64))) (= zx8_{id} zy8_{id}) (= zx8_{id} zx16_{id}))",
        id = id
    ));

    // round 4
    solver.additional_decls.push((
        format!("zret4_{id}", id = id),
        String::from("(_ BitVec 64)"),
    ));
    solver
        .additional_decls
        .push((format!("zy4_{id}", id = id), String::from("(_ BitVec 64)")));
    solver
        .additional_decls
        .push((format!("zx4_{id}", id = id), String::from("(_ BitVec 64)")));

    solver.additional_assumptions.push(format!(
        "(= zy4_{id} (bvlshr zx8_{id} #x0000000000000004))",
        id = id
    ));
    solver.additional_assumptions.push(format!("(ite (not (= zy4_{id} (_ bv0 64))) (= zret4_{id} zret3_{id}) (= zret4_{id} (bvadd zret3_{id} (_ bv4 64))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= zy4_{id} (_ bv0 64))) (= zx4_{id} zy4_{id}) (= zx4_{id} zx8_{id}))",
        id = id
    ));

    // round 5
    solver.additional_decls.push((
        format!("zret5_{id}", id = id),
        String::from("(_ BitVec 64)"),
    ));
    solver
        .additional_decls
        .push((format!("zy2_{id}", id = id), String::from("(_ BitVec 64)")));
    solver
        .additional_decls
        .push((format!("zx2_{id}", id = id), String::from("(_ BitVec 64)")));

    solver.additional_assumptions.push(format!(
        "(= zy2_{id} (bvlshr zx4_{id} #x0000000000000002))",
        id = id
    ));
    solver.additional_assumptions.push(format!("(ite (not (= zy2_{id} (_ bv0 64))) (= zret5_{id} zret4_{id}) (= zret5_{id} (bvadd zret4_{id} (_ bv2 64))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= zy2_{id} (_ bv0 64))) (= zx2_{id} zy2_{id}) (= zx2_{id} zx4_{id}))",
        id = id
    ));

    // round 6
    solver.additional_decls.push((
        format!("zret6_{id}", id = id),
        String::from("(_ BitVec 64)"),
    ));
    solver
        .additional_decls
        .push((format!("zy1_{id}", id = id), String::from("(_ BitVec 64)")));
    solver
        .additional_decls
        .push((format!("zx1_{id}", id = id), String::from("(_ BitVec 64)")));

    solver.additional_assumptions.push(format!(
        "(= zy1_{id} (bvlshr zx2_{id} #x0000000000000001))",
        id = id
    ));
    solver.additional_assumptions.push(format!("(ite (not (= zy1_{id} (_ bv0 64))) (= zret6_{id} zret5_{id}) (= zret6_{id} (bvadd zret5_{id} (_ bv1 64))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= zy1_{id} (_ bv0 64))) (= zx1_{id} zy1_{id}) (= zx1_{id} zx2_{id}))",
        id = id
    ));

    // last round
    solver.additional_decls.push((
        format!("zret7_{id}", id = id),
        String::from("(_ BitVec 64)"),
    ));
    solver.additional_assumptions.push(format!("(ite (not (= zx1_{id} (_ bv0 64))) (= zret7_{id} zret6_{id}) (= zret7_{id} (bvadd zret6_{id} (_ bv1 64))))", id = id));

    solver.additional_decls.push((
        format!("clzret_{id}", id = id),
        String::from("(_ BitVec 64)"),
    ));
    solver.additional_assumptions.push(format!("(ite (= zret7_{id} (_ bv0 64)) (= clzret_{id} zret7_{id}) (= clzret_{id} (bvsub zret7_{id} (_ bv1 64))))", id = id));

    // total zeros counter
    solver.additional_decls.push((
        format!("sret0_{id}", id = id),
        String::from("(_ BitVec 64)"),
    ));
    solver
        .additional_assumptions
        .push(format!("(= sret0_{id} (_ bv0 64))", id = id));

    // round 1
    solver.additional_decls.push((
        format!("sret1_{id}", id = id),
        String::from("(_ BitVec 64)"),
    ));
    solver
        .additional_decls
        .push((format!("sy32_{id}", id = id), String::from("(_ BitVec 64)")));
    solver
        .additional_decls
        .push((format!("sx32_{id}", id = id), String::from("(_ BitVec 64)")));

    solver.additional_assumptions.push(format!(
        "(= sy32_{id} (bvashr {x} #x0000000000000020))",
        x = x,
        id = id
    ));
    solver.additional_assumptions.push(format!("(ite (not (= sy32_{id} (_ bv18446744073709551615 64))) (= sret1_{id} sret0_{id}) (= sret1_{id} (bvadd sret0_{id} (_ bv32 64))))", id = id));
    solver.additional_assumptions.push(format!("(ite (not (= sy32_{id} (_ bv18446744073709551615 64))) (= sx32_{id} sy32_{id}) (= sx32_{id} {x}))", x = x, id = id));

    // round 2
    solver.additional_decls.push((
        format!("sret2_{id}", id = id),
        String::from("(_ BitVec 64)"),
    ));
    solver
        .additional_decls
        .push((format!("sy16_{id}", id = id), String::from("(_ BitVec 64)")));
    solver
        .additional_decls
        .push((format!("sx16_{id}", id = id), String::from("(_ BitVec 64)")));

    solver.additional_assumptions.push(format!(
        "(= sy16_{id} (bvashr sx32_{id} #x0000000000000010))",
        id = id
    ));
    solver.additional_assumptions.push(format!("(ite (not (= sy16_{id} (_ bv18446744073709551615 64))) (= sret2_{id} sret1_{id}) (= sret2_{id} (bvadd sret1_{id} (_ bv16 64))))", id = id));
    solver.additional_assumptions.push(format!("(ite (not (= sy16_{id} (_ bv18446744073709551615 64))) (= sx16_{id} sy16_{id}) (= sx16_{id} sx32_{id}))", id = id));

    // round 3
    solver.additional_decls.push((
        format!("sret3_{id}", id = id),
        String::from("(_ BitVec 64)"),
    ));
    solver
        .additional_decls
        .push((format!("sy8_{id}", id = id), String::from("(_ BitVec 64)")));
    solver
        .additional_decls
        .push((format!("sx8_{id}", id = id), String::from("(_ BitVec 64)")));

    solver.additional_assumptions.push(format!(
        "(= sy8_{id} (bvashr sx16_{id} #x0000000000000008))",
        id = id
    ));
    solver.additional_assumptions.push(format!("(ite (not (= sy8_{id} (_ bv18446744073709551615 64))) (= sret3_{id} sret2_{id}) (= sret3_{id} (bvadd sret2_{id} (_ bv8 64))))", id = id));
    solver.additional_assumptions.push(format!("(ite (not (= sy8_{id} (_ bv18446744073709551615 64))) (= sx8_{id} sy8_{id}) (= sx8_{id} sx16_{id}))", id = id));

    // round 4
    solver.additional_decls.push((
        format!("sret4_{id}", id = id),
        String::from("(_ BitVec 64)"),
    ));
    solver
        .additional_decls
        .push((format!("sy4_{id}", id = id), String::from("(_ BitVec 64)")));
    solver
        .additional_decls
        .push((format!("sx4_{id}", id = id), String::from("(_ BitVec 64)")));

    solver.additional_assumptions.push(format!(
        "(= sy4_{id} (bvashr sx8_{id} #x0000000000000004))",
        id = id
    ));
    solver.additional_assumptions.push(format!("(ite (not (= sy4_{id} (_ bv18446744073709551615 64))) (= sret4_{id} sret3_{id}) (= sret4_{id} (bvadd sret3_{id} (_ bv4 64))))", id = id));
    solver.additional_assumptions.push(format!("(ite (not (= sy4_{id} (_ bv18446744073709551615 64))) (= sx4_{id} sy4_{id}) (= sx4_{id} sx8_{id}))", id = id));

    // round 5
    solver.additional_decls.push((
        format!("sret5_{id}", id = id),
        String::from("(_ BitVec 64)"),
    ));
    solver
        .additional_decls
        .push((format!("sy2_{id}", id = id), String::from("(_ BitVec 64)")));
    solver
        .additional_decls
        .push((format!("sx2_{id}", id = id), String::from("(_ BitVec 64)")));

    solver.additional_assumptions.push(format!(
        "(= sy2_{id} (bvashr sx4_{id} #x0000000000000002))",
        id = id
    ));
    solver.additional_assumptions.push(format!("(ite (not (= sy2_{id} (_ bv18446744073709551615 64))) (= sret5_{id} sret4_{id}) (= sret5_{id} (bvadd sret4_{id} (_ bv2 64))))", id = id));
    solver.additional_assumptions.push(format!("(ite (not (= sy2_{id} (_ bv18446744073709551615 64))) (= sx2_{id} sy2_{id}) (= sx2_{id} sx4_{id}))", id = id));

    // round 6
    solver.additional_decls.push((
        format!("sret6_{id}", id = id),
        String::from("(_ BitVec 64)"),
    ));
    solver
        .additional_decls
        .push((format!("sy1_{id}", id = id), String::from("(_ BitVec 64)")));
    solver
        .additional_decls
        .push((format!("sx1_{id}", id = id), String::from("(_ BitVec 64)")));

    solver.additional_assumptions.push(format!(
        "(= sy1_{id} (bvashr sx2_{id} #x0000000000000001))",
        id = id
    ));
    solver.additional_assumptions.push(format!("(ite (not (= sy1_{id} (_ bv18446744073709551615 64))) (= sret6_{id} sret5_{id}) (= sret6_{id} (bvadd sret5_{id} (_ bv1 64))))", id = id));
    solver.additional_assumptions.push(format!("(ite (not (= sy1_{id} (_ bv18446744073709551615 64))) (= sx1_{id} sy1_{id}) (= sx1_{id} sx2_{id}))", id = id));

    // last round
    solver.additional_decls.push((
        format!("sret7_{id}", id = id),
        String::from("(_ BitVec 64)"),
    ));
    solver.additional_assumptions.push(format!("(ite (not (= sx1_{id} (_ bv18446744073709551615 64))) (= sret7_{id} sret6_{id}) (= sret7_{id} (bvadd sret6_{id} (_ bv1 64))))", id = id));

    solver.additional_decls.push((
        format!("clsret_{id}", id = id),
        String::from("(_ BitVec 64)"),
    ));
    solver.additional_assumptions.push(format!("(ite (= sret7_{id} (_ bv0 64)) (= clsret_{id} sret7_{id}) (= clsret_{id} (bvsub sret7_{id} (_ bv1 64))))", id = id));

    // final return
    solver.additional_decls.push((
        format!("cls64ret_{id}", id = id),
        String::from("(_ BitVec 64)"),
    ));
    solver.additional_assumptions.push(format!(
        "(ite (bvsle (_ bv0 64) {x}) (= cls64ret_{id} clzret_{id}) (= cls64ret_{id} clsret_{id}))",
        x = x,
        id = id
    ));

    format!("cls64ret_{id}", id = id)
}

pub fn cls32(solver: &mut SolverCtx, x: SExpr, id: u32) -> SExpr {
    let x = format!("((_ extract 31 0) {})", x);

    // total zeros counter
    solver.additional_decls.push((
        format!("zret0_{id}", id = id),
        String::from("(_ BitVec 32)"),
    ));
    solver
        .additional_assumptions
        .push(format!("(= zret0_{id} (_ bv0 32))", id = id));

    // round 1
    solver.additional_decls.push((
        format!("zret2_{id}", id = id),
        String::from("(_ BitVec 32)"),
    ));
    solver
        .additional_decls
        .push((format!("zy16_{id}", id = id), String::from("(_ BitVec 32)")));
    solver
        .additional_decls
        .push((format!("zx16_{id}", id = id), String::from("(_ BitVec 32)")));

    solver.additional_assumptions.push(format!(
        "(= zy16_{id} (bvlshr {x} #x00000010))",
        id = id,
        x = x
    ));
    solver.additional_assumptions.push(format!("(ite (not (= zy16_{id} (_ bv0 32))) (= zret2_{id} zret0_{id}) (= zret2_{id} (bvadd zret0_{id} (_ bv16 32))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= zy16_{id} (_ bv0 32))) (= zx16_{id} zy16_{id}) (= zx16_{id} {x}))",
        id = id,
        x = x
    ));

    // round 2
    solver.additional_decls.push((
        format!("zret3_{id}", id = id),
        String::from("(_ BitVec 32)"),
    ));
    solver
        .additional_decls
        .push((format!("zy8_{id}", id = id), String::from("(_ BitVec 32)")));
    solver
        .additional_decls
        .push((format!("zx8_{id}", id = id), String::from("(_ BitVec 32)")));

    solver.additional_assumptions.push(format!(
        "(= zy8_{id} (bvlshr zx16_{id} #x00000008))",
        id = id
    ));
    solver.additional_assumptions.push(format!("(ite (not (= zy8_{id} (_ bv0 32))) (= zret3_{id} zret2_{id}) (= zret3_{id} (bvadd zret2_{id} (_ bv8 32))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= zy8_{id} (_ bv0 32))) (= zx8_{id} zy8_{id}) (= zx8_{id} zx16_{id}))",
        id = id
    ));

    // round 3
    solver.additional_decls.push((
        format!("zret4_{id}", id = id),
        String::from("(_ BitVec 32)"),
    ));
    solver
        .additional_decls
        .push((format!("zy4_{id}", id = id), String::from("(_ BitVec 32)")));
    solver
        .additional_decls
        .push((format!("zx4_{id}", id = id), String::from("(_ BitVec 32)")));

    solver.additional_assumptions.push(format!(
        "(= zy4_{id} (bvlshr zx8_{id} #x00000004))",
        id = id
    ));
    solver.additional_assumptions.push(format!("(ite (not (= zy4_{id} (_ bv0 32))) (= zret4_{id} zret3_{id}) (= zret4_{id} (bvadd zret3_{id} (_ bv4 32))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= zy4_{id} (_ bv0 32))) (= zx4_{id} zy4_{id}) (= zx4_{id} zx8_{id}))",
        id = id
    ));

    // round 4
    solver.additional_decls.push((
        format!("zret5_{id}", id = id),
        String::from("(_ BitVec 32)"),
    ));
    solver
        .additional_decls
        .push((format!("zy2_{id}", id = id), String::from("(_ BitVec 32)")));
    solver
        .additional_decls
        .push((format!("zx2_{id}", id = id), String::from("(_ BitVec 32)")));

    solver.additional_assumptions.push(format!(
        "(= zy2_{id} (bvlshr zx4_{id} #x00000002))",
        id = id
    ));
    solver.additional_assumptions.push(format!("(ite (not (= zy2_{id} (_ bv0 32))) (= zret5_{id} zret4_{id}) (= zret5_{id} (bvadd zret4_{id} (_ bv2 32))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= zy2_{id} (_ bv0 32))) (= zx2_{id} zy2_{id}) (= zx2_{id} zx4_{id}))",
        id = id
    ));

    // round 5
    solver.additional_decls.push((
        format!("zret6_{id}", id = id),
        String::from("(_ BitVec 32)"),
    ));
    solver
        .additional_decls
        .push((format!("zy1_{id}", id = id), String::from("(_ BitVec 32)")));
    solver
        .additional_decls
        .push((format!("zx1_{id}", id = id), String::from("(_ BitVec 32)")));

    solver.additional_assumptions.push(format!(
        "(= zy1_{id} (bvlshr zx2_{id} #x00000001))",
        id = id
    ));
    solver.additional_assumptions.push(format!("(ite (not (= zy1_{id} (_ bv0 32))) (= zret6_{id} zret5_{id}) (= zret6_{id} (bvadd zret5_{id} (_ bv1 32))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= zy1_{id} (_ bv0 32))) (= zx1_{id} zy1_{id}) (= zx1_{id} zx2_{id}))",
        id = id
    ));

    // last round
    solver.additional_decls.push((
        format!("zret7_{id}", id = id),
        String::from("(_ BitVec 32)"),
    ));
    solver.additional_assumptions.push(format!("(ite (not (= zx1_{id} (_ bv0 32))) (= zret7_{id} zret6_{id}) (= zret7_{id} (bvadd zret6_{id} (_ bv1 32))))", id = id));

    solver.additional_decls.push((
        format!("clzret_{id}", id = id),
        String::from("(_ BitVec 32)"),
    ));
    solver.additional_assumptions.push(format!("(ite (= zret7_{id} (_ bv0 32)) (= clzret_{id} zret7_{id}) (= clzret_{id} (bvsub zret7_{id} (_ bv1 32))))", id = id));

    // total zeros counter
    solver.additional_decls.push((
        format!("sret0_{id}", id = id),
        String::from("(_ BitVec 32)"),
    ));
    solver
        .additional_assumptions
        .push(format!("(= sret0_{id} (_ bv0 32))", id = id));

    // round 1
    solver.additional_decls.push((
        format!("sret2_{id}", id = id),
        String::from("(_ BitVec 32)"),
    ));
    solver
        .additional_decls
        .push((format!("sy16_{id}", id = id), String::from("(_ BitVec 32)")));
    solver
        .additional_decls
        .push((format!("sx16_{id}", id = id), String::from("(_ BitVec 32)")));

    solver.additional_assumptions.push(format!(
        "(= sy16_{id} (bvashr {x} #x00000010))",
        id = id,
        x = x
    ));
    solver.additional_assumptions.push(format!("(ite (not (= sy16_{id} (_ bv4294967295 32))) (= sret2_{id} sret0_{id}) (= sret2_{id} (bvadd sret0_{id} (_ bv16 32))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= sy16_{id} (_ bv4294967295 32))) (= sx16_{id} sy16_{id}) (= sx16_{id} {x}))",
        id = id,
        x = x
    ));

    // round 2
    solver.additional_decls.push((
        format!("sret3_{id}", id = id),
        String::from("(_ BitVec 32)"),
    ));
    solver
        .additional_decls
        .push((format!("sy8_{id}", id = id), String::from("(_ BitVec 32)")));
    solver
        .additional_decls
        .push((format!("sx8_{id}", id = id), String::from("(_ BitVec 32)")));

    solver.additional_assumptions.push(format!(
        "(= sy8_{id} (bvashr sx16_{id} #x00000008))",
        id = id
    ));
    solver.additional_assumptions.push(format!("(ite (not (= sy8_{id} (_ bv4294967295 32))) (= sret3_{id} sret2_{id}) (= sret3_{id} (bvadd sret2_{id} (_ bv8 32))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= sy8_{id} (_ bv4294967295 32))) (= sx8_{id} sy8_{id}) (= sx8_{id} sx16_{id}))",
        id = id
    ));

    // round 3
    solver.additional_decls.push((
        format!("sret4_{id}", id = id),
        String::from("(_ BitVec 32)"),
    ));
    solver
        .additional_decls
        .push((format!("sy4_{id}", id = id), String::from("(_ BitVec 32)")));
    solver
        .additional_decls
        .push((format!("sx4_{id}", id = id), String::from("(_ BitVec 32)")));

    solver.additional_assumptions.push(format!(
        "(= sy4_{id} (bvashr sx8_{id} #x00000004))",
        id = id
    ));
    solver.additional_assumptions.push(format!("(ite (not (= sy4_{id} (_ bv4294967295 32))) (= sret4_{id} sret3_{id}) (= sret4_{id} (bvadd sret3_{id} (_ bv4 32))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= sy4_{id} (_ bv4294967295 32))) (= sx4_{id} sy4_{id}) (= sx4_{id} sx8_{id}))",
        id = id
    ));

    // round 4
    solver.additional_decls.push((
        format!("sret5_{id}", id = id),
        String::from("(_ BitVec 32)"),
    ));
    solver
        .additional_decls
        .push((format!("sy2_{id}", id = id), String::from("(_ BitVec 32)")));
    solver
        .additional_decls
        .push((format!("sx2_{id}", id = id), String::from("(_ BitVec 32)")));

    solver.additional_assumptions.push(format!(
        "(= sy2_{id} (bvashr sx4_{id} #x00000002))",
        id = id
    ));
    solver.additional_assumptions.push(format!("(ite (not (= sy2_{id} (_ bv4294967295 32))) (= sret5_{id} sret4_{id}) (= sret5_{id} (bvadd sret4_{id} (_ bv2 32))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= sy2_{id} (_ bv4294967295 32))) (= sx2_{id} sy2_{id}) (= sx2_{id} sx4_{id}))",
        id = id
    ));

    // round 5
    solver.additional_decls.push((
        format!("sret6_{id}", id = id),
        String::from("(_ BitVec 32)"),
    ));
    solver
        .additional_decls
        .push((format!("sy1_{id}", id = id), String::from("(_ BitVec 32)")));
    solver
        .additional_decls
        .push((format!("sx1_{id}", id = id), String::from("(_ BitVec 32)")));

    solver.additional_assumptions.push(format!(
        "(= sy1_{id} (bvashr sx2_{id} #x00000001))",
        id = id
    ));
    solver.additional_assumptions.push(format!("(ite (not (= sy1_{id} (_ bv4294967295 32))) (= sret6_{id} sret5_{id}) (= sret6_{id} (bvadd sret5_{id} (_ bv1 32))))", id = id));
    solver.additional_assumptions.push(format!(
        "(ite (not (= sy1_{id} (_ bv4294967295 32))) (= sx1_{id} sy1_{id}) (= sx1_{id} sx2_{id}))",
        id = id
    ));

    // last round
    solver.additional_decls.push((
        format!("sret7_{id}", id = id),
        String::from("(_ BitVec 32)"),
    ));
    solver.additional_assumptions.push(format!("(ite (not (= sx1_{id} (_ bv4294967295 32))) (= sret7_{id} sret6_{id}) (= sret7_{id} (bvadd sret6_{id} (_ bv1 32))))", id = id));

    solver.additional_decls.push((
        format!("clsret_{id}", id = id),
        String::from("(_ BitVec 32)"),
    ));
    solver.additional_assumptions.push(format!("(ite (= sret7_{id} (_ bv0 32)) (= clsret_{id} sret7_{id}) (= clsret_{id} (bvsub sret7_{id} (_ bv1 32))))", id = id));

    // final return
    solver.additional_decls.push((
        format!("cls32ret_{id}", id = id),
        String::from("(_ BitVec 32)"),
    ));
    solver.additional_assumptions.push(format!(
        "(ite (bvsle (_ bv0 32) {x}) (= cls32ret_{id} clzret_{id}) (= cls32ret_{id} clsret_{id}))",
        id = id,
        x = x
    ));

    let padding = solver.new_fresh_bits(solver.bitwidth - 32);
    format!(
        "(concat {padding} cls32ret_{id})",
        padding = padding,
        id = id
    )
}

pub fn cls16(solver: &mut SolverCtx, x: SExpr, id: u32) -> SExpr {
    let x = format!("((_ extract 15 0) {})", x);

    // Generated code.
    // total zeros counter
    let zret0 = solver.declare(format!("zret0_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(16)]));
    solver.assume(solver.smt.eq(zret0, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv0"), solver.smt.numeral(16)])));
    // round 1
    let zret3 = solver.declare(format!("zret3_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(16)]));
    let zy8 = solver.declare(format!("zy8_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(16)]));
    let zx8 = solver.declare(format!("zx8_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(16)]));
    solver.assume(solver.smt.eq(zy8, solver.smt.bvlshr(x, solver.smt.atom("#x0008"))));
    solver.assume(solver.smt.list(vec![solver.smt.atom("ite"), solver.smt.list(vec![solver.smt.atom("not"), solver.smt.eq(zy8, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv0"), solver.smt.numeral(16)]))]), solver.smt.eq(zret3, zret0), solver.smt.eq(zret3, solver.smt.list(vec![solver.smt.atom("bvadd"), zret0, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv8"), solver.smt.numeral(16)])]))]));
    solver.assume(solver.smt.list(vec![solver.smt.atom("ite"), solver.smt.list(vec![solver.smt.atom("not"), solver.smt.eq(zy8, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv0"), solver.smt.numeral(16)]))]), solver.smt.eq(zx8, zy8), solver.smt.eq(zx8, x)]));
    // round 2
    let zret4 = solver.declare(format!("zret4_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(16)]));
    let zy4 = solver.declare(format!("zy4_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(16)]));
    let zx4 = solver.declare(format!("zx4_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(16)]));
    solver.assume(solver.smt.eq(zy4, solver.smt.bvlshr(zx8, solver.smt.atom("#x0004"))));
    solver.assume(solver.smt.list(vec![solver.smt.atom("ite"), solver.smt.list(vec![solver.smt.atom("not"), solver.smt.eq(zy4, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv0"), solver.smt.numeral(16)]))]), solver.smt.eq(zret4, zret3), solver.smt.eq(zret4, solver.smt.list(vec![solver.smt.atom("bvadd"), zret3, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv4"), solver.smt.numeral(16)])]))]));
    solver.assume(solver.smt.list(vec![solver.smt.atom("ite"), solver.smt.list(vec![solver.smt.atom("not"), solver.smt.eq(zy4, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv0"), solver.smt.numeral(16)]))]), solver.smt.eq(zx4, zy4), solver.smt.eq(zx4, zx8)]));
    // round 3
    let zret5 = solver.declare(format!("zret5_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(16)]));
    let zy2 = solver.declare(format!("zy2_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(16)]));
    let zx2 = solver.declare(format!("zx2_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(16)]));
    solver.assume(solver.smt.eq(zy2, solver.smt.bvlshr(zx4, solver.smt.atom("#x0002"))));
    solver.assume(solver.smt.list(vec![solver.smt.atom("ite"), solver.smt.list(vec![solver.smt.atom("not"), solver.smt.eq(zy2, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv0"), solver.smt.numeral(16)]))]), solver.smt.eq(zret5, zret4), solver.smt.eq(zret5, solver.smt.list(vec![solver.smt.atom("bvadd"), zret4, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv2"), solver.smt.numeral(16)])]))]));
    solver.assume(solver.smt.list(vec![solver.smt.atom("ite"), solver.smt.list(vec![solver.smt.atom("not"), solver.smt.eq(zy2, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv0"), solver.smt.numeral(16)]))]), solver.smt.eq(zx2, zy2), solver.smt.eq(zx2, zx4)]));
    // round 4
    let zret6 = solver.declare(format!("zret6_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(16)]));
    let zy1 = solver.declare(format!("zy1_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(16)]));
    let zx1 = solver.declare(format!("zx1_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(16)]));
    solver.assume(solver.smt.eq(zy1, solver.smt.bvlshr(zx2, solver.smt.atom("#x0001"))));
    solver.assume(solver.smt.list(vec![solver.smt.atom("ite"), solver.smt.list(vec![solver.smt.atom("not"), solver.smt.eq(zy1, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv0"), solver.smt.numeral(16)]))]), solver.smt.eq(zret6, zret5), solver.smt.eq(zret6, solver.smt.list(vec![solver.smt.atom("bvadd"), zret5, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv1"), solver.smt.numeral(16)])]))]));
    solver.assume(solver.smt.list(vec![solver.smt.atom("ite"), solver.smt.list(vec![solver.smt.atom("not"), solver.smt.eq(zy1, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv0"), solver.smt.numeral(16)]))]), solver.smt.eq(zx1, zy1), solver.smt.eq(zx1, zx2)]));
    // last round
    let zret7 = solver.declare(format!("zret7_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(16)]));
    solver.assume(solver.smt.list(vec![solver.smt.atom("ite"), solver.smt.list(vec![solver.smt.atom("not"), solver.smt.eq(zx1, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv0"), solver.smt.numeral(16)]))]), solver.smt.eq(zret7, zret6), solver.smt.eq(zret7, solver.smt.list(vec![solver.smt.atom("bvadd"), zret6, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv1"), solver.smt.numeral(16)])]))]));
    let clzret = solver.declare(format!("clzret_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(16)]));
    solver.assume(solver.smt.list(vec![solver.smt.atom("ite"), solver.smt.eq(zret7, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv0"), solver.smt.numeral(16)])), solver.smt.eq(clzret, zret7), solver.smt.eq(clzret, solver.smt.list(vec![solver.smt.atom("bvsub"), zret7, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv1"), solver.smt.numeral(16)])]))]));
    // total zeros counter
    let sret0 = solver.declare(format!("sret0_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(16)]));
    solver.assume(solver.smt.eq(sret0, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv0"), solver.smt.numeral(16)])));
    // round 1
    let sret3 = solver.declare(format!("sret3_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(16)]));
    let sy8 = solver.declare(format!("sy8_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(16)]));
    let sx8 = solver.declare(format!("sx8_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(16)]));
    solver.assume(solver.smt.eq(sy8, solver.smt.bvashr(x, solver.smt.atom("#x0008"))));
    solver.assume(solver.smt.list(vec![solver.smt.atom("ite"), solver.smt.list(vec![solver.smt.atom("not"), solver.smt.eq(sy8, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv65535"), solver.smt.numeral(16)]))]), solver.smt.eq(sret3, sret0), solver.smt.eq(sret3, solver.smt.list(vec![solver.smt.atom("bvadd"), sret0, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv8"), solver.smt.numeral(16)])]))]));
    solver.assume(solver.smt.list(vec![solver.smt.atom("ite"), solver.smt.list(vec![solver.smt.atom("not"), solver.smt.eq(sy8, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv65535"), solver.smt.numeral(16)]))]), solver.smt.eq(sx8, sy8), solver.smt.eq(sx8, x)]));
    // round 2
    let sret4 = solver.declare(format!("sret4_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(16)]));
    let sy4 = solver.declare(format!("sy4_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(16)]));
    let sx4 = solver.declare(format!("sx4_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(16)]));
    solver.assume(solver.smt.eq(sy4, solver.smt.bvashr(sx8, solver.smt.atom("#x0004"))));
    solver.assume(solver.smt.list(vec![solver.smt.atom("ite"), solver.smt.list(vec![solver.smt.atom("not"), solver.smt.eq(sy4, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv65535"), solver.smt.numeral(16)]))]), solver.smt.eq(sret4, sret3), solver.smt.eq(sret4, solver.smt.list(vec![solver.smt.atom("bvadd"), sret3, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv4"), solver.smt.numeral(16)])]))]));
    solver.assume(solver.smt.list(vec![solver.smt.atom("ite"), solver.smt.list(vec![solver.smt.atom("not"), solver.smt.eq(sy4, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv65535"), solver.smt.numeral(16)]))]), solver.smt.eq(sx4, sy4), solver.smt.eq(sx4, sx8)]));
    // round 3
    let sret5 = solver.declare(format!("sret5_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(16)]));
    let sy2 = solver.declare(format!("sy2_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(16)]));
    let sx2 = solver.declare(format!("sx2_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(16)]));
    solver.assume(solver.smt.eq(sy2, solver.smt.bvashr(sx4, solver.smt.atom("#x0002"))));
    solver.assume(solver.smt.list(vec![solver.smt.atom("ite"), solver.smt.list(vec![solver.smt.atom("not"), solver.smt.eq(sy2, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv65535"), solver.smt.numeral(16)]))]), solver.smt.eq(sret5, sret4), solver.smt.eq(sret5, solver.smt.list(vec![solver.smt.atom("bvadd"), sret4, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv2"), solver.smt.numeral(16)])]))]));
    solver.assume(solver.smt.list(vec![solver.smt.atom("ite"), solver.smt.list(vec![solver.smt.atom("not"), solver.smt.eq(sy2, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv65535"), solver.smt.numeral(16)]))]), solver.smt.eq(sx2, sy2), solver.smt.eq(sx2, sx4)]));
    // round 4
    let sret6 = solver.declare(format!("sret6_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(16)]));
    let sy1 = solver.declare(format!("sy1_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(16)]));
    let sx1 = solver.declare(format!("sx1_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(16)]));
    solver.assume(solver.smt.eq(sy1, solver.smt.bvashr(sx2, solver.smt.atom("#x0001"))));
    solver.assume(solver.smt.list(vec![solver.smt.atom("ite"), solver.smt.list(vec![solver.smt.atom("not"), solver.smt.eq(sy1, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv65535"), solver.smt.numeral(16)]))]), solver.smt.eq(sret6, sret5), solver.smt.eq(sret6, solver.smt.list(vec![solver.smt.atom("bvadd"), sret5, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv1"), solver.smt.numeral(16)])]))]));
    solver.assume(solver.smt.list(vec![solver.smt.atom("ite"), solver.smt.list(vec![solver.smt.atom("not"), solver.smt.eq(sy1, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv65535"), solver.smt.numeral(16)]))]), solver.smt.eq(sx1, sy1), solver.smt.eq(sx1, sx2)]));
    // last round
    let sret7 = solver.declare(format!("sret7_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(16)]));
    solver.assume(solver.smt.list(vec![solver.smt.atom("ite"), solver.smt.list(vec![solver.smt.atom("not"), solver.smt.eq(sx1, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv65535"), solver.smt.numeral(16)]))]), solver.smt.eq(sret7, sret6), solver.smt.eq(sret7, solver.smt.list(vec![solver.smt.atom("bvadd"), sret6, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv1"), solver.smt.numeral(16)])]))]));
    let clsret = solver.declare(format!("clsret_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(16)]));
    solver.assume(solver.smt.list(vec![solver.smt.atom("ite"), solver.smt.eq(sret7, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv0"), solver.smt.numeral(16)])), solver.smt.eq(clsret, sret7), solver.smt.eq(clsret, solver.smt.list(vec![solver.smt.atom("bvsub"), sret7, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv1"), solver.smt.numeral(16)])]))]));
    let cls16ret = solver.declare(format!("cls16ret_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(16)]));
    solver.assume(solver.smt.list(vec![solver.smt.atom("ite"), solver.smt.list(vec![solver.smt.atom("bvsle"), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv0"), solver.smt.numeral(16)]), x]), solver.smt.eq(cls16ret, clzret), solver.smt.eq(cls16ret, clsret)]));

    let padding = solver.new_fresh_bits(solver.bitwidth - 16);
    solver.smt.concat(padding, cls16ret)
}

pub fn cls8(solver: &mut SolverCtx, x: SExpr, id: u32) -> SExpr {
    let x = solver.smt.extract(7, 0, x);
    
    // Generated code.
    // total zeros counter
    let zret0 = solver.declare(format!("zret0_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(8)]));
    solver.assume(solver.smt.eq(zret0, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv0"), solver.smt.numeral(8)])));
    // round 1
    let zret4 = solver.declare(format!("zret4_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(8)]));
    let zy4 = solver.declare(format!("zy4_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(8)]));
    let zx4 = solver.declare(format!("zx4_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(8)]));
    solver.assume(solver.smt.eq(zy4, solver.smt.bvlshr(x, solver.smt.atom("#x04"))));
    solver.assume(solver.smt.list(vec![solver.smt.atom("ite"), solver.smt.list(vec![solver.smt.atom("not"), solver.smt.eq(zy4, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv0"), solver.smt.numeral(8)]))]), solver.smt.eq(zret4, zret0), solver.smt.eq(zret4, solver.smt.list(vec![solver.smt.atom("bvadd"), zret0, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv4"), solver.smt.numeral(8)])]))]));
    solver.assume(solver.smt.list(vec![solver.smt.atom("ite"), solver.smt.list(vec![solver.smt.atom("not"), solver.smt.eq(zy4, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv0"), solver.smt.numeral(8)]))]), solver.smt.eq(zx4, zy4), solver.smt.eq(zx4, x)]));
    // round 2
    let zret5 = solver.declare(format!("zret5_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(8)]));
    let zy2 = solver.declare(format!("zy2_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(8)]));
    let zx2 = solver.declare(format!("zx2_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(8)]));
    solver.assume(solver.smt.eq(zy2, solver.smt.bvlshr(zx4, solver.smt.atom("#x02"))));
    solver.assume(solver.smt.list(vec![solver.smt.atom("ite"), solver.smt.list(vec![solver.smt.atom("not"), solver.smt.eq(zy2, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv0"), solver.smt.numeral(8)]))]), solver.smt.eq(zret5, zret4), solver.smt.eq(zret5, solver.smt.list(vec![solver.smt.atom("bvadd"), zret4, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv2"), solver.smt.numeral(8)])]))]));
    solver.assume(solver.smt.list(vec![solver.smt.atom("ite"), solver.smt.list(vec![solver.smt.atom("not"), solver.smt.eq(zy2, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv0"), solver.smt.numeral(8)]))]), solver.smt.eq(zx2, zy2), solver.smt.eq(zx2, zx4)]));
    // round 3
    let zret6 = solver.declare(format!("zret6_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(8)]));
    let zy1 = solver.declare(format!("zy1_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(8)]));
    let zx1 = solver.declare(format!("zx1_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(8)]));
    solver.assume(solver.smt.eq(zy1, solver.smt.bvlshr(zx2, solver.smt.atom("#x01"))));
    solver.assume(solver.smt.list(vec![solver.smt.atom("ite"), solver.smt.list(vec![solver.smt.atom("not"), solver.smt.eq(zy1, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv0"), solver.smt.numeral(8)]))]), solver.smt.eq(zret6, zret5), solver.smt.eq(zret6, solver.smt.list(vec![solver.smt.atom("bvadd"), zret5, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv1"), solver.smt.numeral(8)])]))]));
    solver.assume(solver.smt.list(vec![solver.smt.atom("ite"), solver.smt.list(vec![solver.smt.atom("not"), solver.smt.eq(zy1, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv0"), solver.smt.numeral(8)]))]), solver.smt.eq(zx1, zy1), solver.smt.eq(zx1, zx2)]));
    // last round
    let zret7 = solver.declare(format!("zret7_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(8)]));
    solver.assume(solver.smt.list(vec![solver.smt.atom("ite"), solver.smt.list(vec![solver.smt.atom("not"), solver.smt.eq(zx1, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv0"), solver.smt.numeral(8)]))]), solver.smt.eq(zret7, zret6), solver.smt.eq(zret7, solver.smt.list(vec![solver.smt.atom("bvadd"), zret6, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv1"), solver.smt.numeral(8)])]))]));
    let clzret = solver.declare(format!("clzret_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(8)]));
    solver.assume(solver.smt.list(vec![solver.smt.atom("ite"), solver.smt.eq(zret7, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv0"), solver.smt.numeral(8)])), solver.smt.eq(clzret, zret7), solver.smt.eq(clzret, solver.smt.list(vec![solver.smt.atom("bvsub"), zret7, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv1"), solver.smt.numeral(8)])]))]));
    // total zeros counter
    let sret0 = solver.declare(format!("sret0_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(8)]));
    solver.assume(solver.smt.eq(sret0, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv0"), solver.smt.numeral(8)])));
    // round 1
    let sret4 = solver.declare(format!("sret4_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(8)]));
    let sy4 = solver.declare(format!("sy4_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(8)]));
    let sx4 = solver.declare(format!("sx4_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(8)]));
    solver.assume(solver.smt.eq(sy4, solver.smt.bvashr(x, solver.smt.atom("#x04"))));
    solver.assume(solver.smt.list(vec![solver.smt.atom("ite"), solver.smt.list(vec![solver.smt.atom("not"), solver.smt.eq(sy4, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv255"), solver.smt.numeral(8)]))]), solver.smt.eq(sret4, sret0), solver.smt.eq(sret4, solver.smt.list(vec![solver.smt.atom("bvadd"), sret0, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv4"), solver.smt.numeral(8)])]))]));
    solver.assume(solver.smt.list(vec![solver.smt.atom("ite"), solver.smt.list(vec![solver.smt.atom("not"), solver.smt.eq(sy4, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv255"), solver.smt.numeral(8)]))]), solver.smt.eq(sx4, sy4), solver.smt.eq(sx4, x)]));
    // round 2
    let sret5 = solver.declare(format!("sret5_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(8)]));
    let sy2 = solver.declare(format!("sy2_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(8)]));
    let sx2 = solver.declare(format!("sx2_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(8)]));
    solver.assume(solver.smt.eq(sy2, solver.smt.bvashr(sx4, solver.smt.atom("#x02"))));
    solver.assume(solver.smt.list(vec![solver.smt.atom("ite"), solver.smt.list(vec![solver.smt.atom("not"), solver.smt.eq(sy2, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv255"), solver.smt.numeral(8)]))]), solver.smt.eq(sret5, sret4), solver.smt.eq(sret5, solver.smt.list(vec![solver.smt.atom("bvadd"), sret4, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv2"), solver.smt.numeral(8)])]))]));
    solver.assume(solver.smt.list(vec![solver.smt.atom("ite"), solver.smt.list(vec![solver.smt.atom("not"), solver.smt.eq(sy2, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv255"), solver.smt.numeral(8)]))]), solver.smt.eq(sx2, sy2), solver.smt.eq(sx2, sx4)]));
    // round 3
    let sret6 = solver.declare(format!("sret6_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(8)]));
    let sy1 = solver.declare(format!("sy1_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(8)]));
    let sx1 = solver.declare(format!("sx1_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(8)]));
    solver.assume(solver.smt.eq(sy1, solver.smt.bvashr(sx2, solver.smt.atom("#x01"))));
    solver.assume(solver.smt.list(vec![solver.smt.atom("ite"), solver.smt.list(vec![solver.smt.atom("not"), solver.smt.eq(sy1, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv255"), solver.smt.numeral(8)]))]), solver.smt.eq(sret6, sret5), solver.smt.eq(sret6, solver.smt.list(vec![solver.smt.atom("bvadd"), sret5, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv1"), solver.smt.numeral(8)])]))]));
    solver.assume(solver.smt.list(vec![solver.smt.atom("ite"), solver.smt.list(vec![solver.smt.atom("not"), solver.smt.eq(sy1, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv255"), solver.smt.numeral(8)]))]), solver.smt.eq(sx1, sy1), solver.smt.eq(sx1, sx2)]));
    // last round
    let sret7 = solver.declare(format!("sret7_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(8)]));
    solver.assume(solver.smt.list(vec![solver.smt.atom("ite"), solver.smt.list(vec![solver.smt.atom("not"), solver.smt.eq(sx1, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv255"), solver.smt.numeral(8)]))]), solver.smt.eq(sret7, sret6), solver.smt.eq(sret7, solver.smt.list(vec![solver.smt.atom("bvadd"), sret6, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv1"), solver.smt.numeral(8)])]))]));
    let clsret = solver.declare(format!("clsret_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(8)]));
    solver.assume(solver.smt.list(vec![solver.smt.atom("ite"), solver.smt.eq(sret7, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv0"), solver.smt.numeral(8)])), solver.smt.eq(clsret, sret7), solver.smt.eq(clsret, solver.smt.list(vec![solver.smt.atom("bvsub"), sret7, solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv1"), solver.smt.numeral(8)])]))]));
    let cls8ret = solver.declare(format!("cls8ret_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(8)]));
    solver.assume(solver.smt.list(vec![solver.smt.atom("ite"), solver.smt.list(vec![solver.smt.atom("bvsle"), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("bv0"), solver.smt.numeral(8)]), x]), solver.smt.eq(cls8ret, clzret), solver.smt.eq(cls8ret, clsret)]));

    let padding = solver.new_fresh_bits(solver.bitwidth - 8);
    solver.smt.concat(padding, cls8ret)
}

pub fn cls1(solver: &mut SolverCtx, id: u32) -> SExpr {
    // Generated code.
    let cls1ret = solver.declare(format!("cls1ret_{id}", id = id), solver.smt.list(vec![solver.smt.atoms().und, solver.smt.atom("BitVec"), solver.smt.numeral(1)]));
    solver.assume(solver.smt.eq(cls1ret, x));
    
    let padding = solver.new_fresh_bits(solver.bitwidth - 1);
    solver.smt.concat(padding, cls1ret)
}
