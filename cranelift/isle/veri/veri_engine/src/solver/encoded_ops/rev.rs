use crate::solver::SolverCtx;
use easy_smt::{Response, SExpr};

pub fn rbit32(solver: &mut SolverCtx, x: SExpr, id: u32) -> SExpr {
    // Don't have an input SMT file for this one?
    todo!();
}

pub fn rev64(solver: &mut SolverCtx, x: SExpr, id: u32) -> SExpr {
    // Generated code.
    let x1 = solver.declare(
        format!("x1_{id}", id = id),
        solver.smt.list(vec![
            solver.smt.atoms().und,
            solver.smt.atom("BitVec"),
            solver.smt.numeral(64),
        ]),
    );
    solver.assume(solver.smt.eq(
        x1,
        solver.smt.bvor(
            solver.smt.bvlshr(x, solver.smt.atom("#x0000000000000020")),
            solver.smt.bvshl(x, solver.smt.atom("#x0000000000000020")),
        ),
    ));
    let x2 = solver.declare(
        format!("x2_{id}", id = id),
        solver.smt.list(vec![
            solver.smt.atoms().und,
            solver.smt.atom("BitVec"),
            solver.smt.numeral(64),
        ]),
    );
    solver.assume(solver.smt.eq(
        x2,
        solver.smt.bvor(
            solver.smt.bvlshr(
                solver.smt.bvand(x1, solver.smt.atom("#xffff0000ffff0000")),
                solver.smt.atom("#x0000000000000010"),
            ),
            solver.smt.bvshl(
                solver.smt.bvand(x1, solver.smt.atom("#x0000ffff0000ffff")),
                solver.smt.atom("#x0000000000000010"),
            ),
        ),
    ));
    let x3 = solver.declare(
        format!("x3_{id}", id = id),
        solver.smt.list(vec![
            solver.smt.atoms().und,
            solver.smt.atom("BitVec"),
            solver.smt.numeral(64),
        ]),
    );
    solver.assume(solver.smt.eq(
        x3,
        solver.smt.bvor(
            solver.smt.bvlshr(
                solver.smt.bvand(x2, solver.smt.atom("#xff00ff00ff00ff00")),
                solver.smt.atom("#x0000000000000008"),
            ),
            solver.smt.bvshl(
                solver.smt.bvand(x2, solver.smt.atom("#x00ff00ff00ff00ff")),
                solver.smt.atom("#x0000000000000008"),
            ),
        ),
    ));
    let x4 = solver.declare(
        format!("x4_{id}", id = id),
        solver.smt.list(vec![
            solver.smt.atoms().und,
            solver.smt.atom("BitVec"),
            solver.smt.numeral(64),
        ]),
    );
    solver.assume(solver.smt.eq(
        x4,
        solver.smt.bvor(
            solver.smt.bvlshr(
                solver.smt.bvand(x3, solver.smt.atom("#xf0f0f0f0f0f0f0f0")),
                solver.smt.atom("#x0000000000000004"),
            ),
            solver.smt.bvshl(
                solver.smt.bvand(x3, solver.smt.atom("#x0f0f0f0f0f0f0f0f")),
                solver.smt.atom("#x0000000000000004"),
            ),
        ),
    ));
    let x5 = solver.declare(
        format!("x5_{id}", id = id),
        solver.smt.list(vec![
            solver.smt.atoms().und,
            solver.smt.atom("BitVec"),
            solver.smt.numeral(64),
        ]),
    );
    solver.assume(solver.smt.eq(
        x5,
        solver.smt.bvor(
            solver.smt.bvlshr(
                solver.smt.bvand(x4, solver.smt.atom("#xcccccccccccccccc")),
                solver.smt.atom("#x0000000000000002"),
            ),
            solver.smt.bvshl(
                solver.smt.bvand(x4, solver.smt.atom("#x3333333333333333")),
                solver.smt.atom("#x0000000000000002"),
            ),
        ),
    ));
    let rev64ret = solver.declare(
        format!("rev64ret_{id}", id = id),
        solver.smt.list(vec![
            solver.smt.atoms().und,
            solver.smt.atom("BitVec"),
            solver.smt.numeral(64),
        ]),
    );
    solver.assume(solver.smt.eq(
        rev64ret,
        solver.smt.bvor(
            solver.smt.bvlshr(
                solver.smt.bvand(x5, solver.smt.atom("#xaaaaaaaaaaaaaaaa")),
                solver.smt.atom("#x0000000000000001"),
            ),
            solver.smt.bvshl(
                solver.smt.bvand(x5, solver.smt.atom("#x5555555555555555")),
                solver.smt.atom("#x0000000000000001"),
            ),
        ),
    ));

    rev64ret
}

pub fn rev32(solver: &mut SolverCtx, x: SExpr, id: u32) -> SExpr {
    let x = solver.smt.extract(31, 0, x);

    // Generated code.
    let x1 = solver.declare(
        format!("x1_{id}", id = id),
        solver.smt.list(vec![
            solver.smt.atoms().und,
            solver.smt.atom("BitVec"),
            solver.smt.numeral(32),
        ]),
    );
    solver.assume(solver.smt.eq(
        x1,
        solver.smt.bvor(
            solver.smt.bvlshr(x, solver.smt.atom("#x00000010")),
            solver.smt.bvshl(x, solver.smt.atom("#x00000010")),
        ),
    ));
    let x2 = solver.declare(
        format!("x2_{id}", id = id),
        solver.smt.list(vec![
            solver.smt.atoms().und,
            solver.smt.atom("BitVec"),
            solver.smt.numeral(32),
        ]),
    );
    solver.assume(solver.smt.eq(
        x2,
        solver.smt.bvor(
            solver.smt.bvlshr(
                solver.smt.bvand(x1, solver.smt.atom("#xff00ff00")),
                solver.smt.atom("#x00000008"),
            ),
            solver.smt.bvshl(
                solver.smt.bvand(x1, solver.smt.atom("#x00ff00ff")),
                solver.smt.atom("#x00000008"),
            ),
        ),
    ));
    let x3 = solver.declare(
        format!("x3_{id}", id = id),
        solver.smt.list(vec![
            solver.smt.atoms().und,
            solver.smt.atom("BitVec"),
            solver.smt.numeral(32),
        ]),
    );
    solver.assume(solver.smt.eq(
        x3,
        solver.smt.bvor(
            solver.smt.bvlshr(
                solver.smt.bvand(x2, solver.smt.atom("#xf0f0f0f0")),
                solver.smt.atom("#x00000004"),
            ),
            solver.smt.bvshl(
                solver.smt.bvand(x2, solver.smt.atom("#x0f0f0f0f")),
                solver.smt.atom("#x00000004"),
            ),
        ),
    ));
    let x4 = solver.declare(
        format!("x4_{id}", id = id),
        solver.smt.list(vec![
            solver.smt.atoms().und,
            solver.smt.atom("BitVec"),
            solver.smt.numeral(32),
        ]),
    );
    solver.assume(solver.smt.eq(
        x4,
        solver.smt.bvor(
            solver.smt.bvlshr(
                solver.smt.bvand(x3, solver.smt.atom("#xcccccccc")),
                solver.smt.atom("#x00000002"),
            ),
            solver.smt.bvshl(
                solver.smt.bvand(x3, solver.smt.atom("#x33333333")),
                solver.smt.atom("#x00000002"),
            ),
        ),
    ));
    let rev32ret = solver.declare(
        format!("rev32ret_{id}", id = id),
        solver.smt.list(vec![
            solver.smt.atoms().und,
            solver.smt.atom("BitVec"),
            solver.smt.numeral(32),
        ]),
    );
    solver.assume(solver.smt.eq(
        rev32ret,
        solver.smt.bvor(
            solver.smt.bvlshr(
                solver.smt.bvand(x4, solver.smt.atom("#xaaaaaaaa")),
                solver.smt.atom("#x00000001"),
            ),
            solver.smt.bvshl(
                solver.smt.bvand(x4, solver.smt.atom("#x55555555")),
                solver.smt.atom("#x00000001"),
            ),
        ),
    ));

    let padding = solver.new_fresh_bits(solver.bitwidth - 32);
    solver.smt.concat(padding, rev32ret)
}

pub fn rev16(solver: &mut SolverCtx, x: SExpr, id: u32) -> SExpr {
    let x = solver.smt.extract(15, 0, x);

    // Generated code.
    let x1 = solver.declare(
        format!("x1_{id}", id = id),
        solver.smt.list(vec![
            solver.smt.atoms().und,
            solver.smt.atom("BitVec"),
            solver.smt.numeral(16),
        ]),
    );
    solver.assume(solver.smt.eq(
        x1,
        solver.smt.bvor(
            solver.smt.bvlshr(x, solver.smt.atom("#x0008")),
            solver.smt.bvshl(x, solver.smt.atom("#x0008")),
        ),
    ));
    let x2 = solver.declare(
        format!("x2_{id}", id = id),
        solver.smt.list(vec![
            solver.smt.atoms().und,
            solver.smt.atom("BitVec"),
            solver.smt.numeral(16),
        ]),
    );
    solver.assume(solver.smt.eq(
        x2,
        solver.smt.bvor(
            solver.smt.bvlshr(
                solver.smt.bvand(x1, solver.smt.atom("#xf0f0")),
                solver.smt.atom("#x0004"),
            ),
            solver.smt.bvshl(
                solver.smt.bvand(x1, solver.smt.atom("#x0f0f")),
                solver.smt.atom("#x0004"),
            ),
        ),
    ));
    let x3 = solver.declare(
        format!("x3_{id}", id = id),
        solver.smt.list(vec![
            solver.smt.atoms().und,
            solver.smt.atom("BitVec"),
            solver.smt.numeral(16),
        ]),
    );
    solver.assume(solver.smt.eq(
        x3,
        solver.smt.bvor(
            solver.smt.bvlshr(
                solver.smt.bvand(x2, solver.smt.atom("#xcccc")),
                solver.smt.atom("#x0002"),
            ),
            solver.smt.bvshl(
                solver.smt.bvand(x2, solver.smt.atom("#x3333")),
                solver.smt.atom("#x0002"),
            ),
        ),
    ));
    let rev16ret = solver.declare(
        format!("rev16ret_{id}", id = id),
        solver.smt.list(vec![
            solver.smt.atoms().und,
            solver.smt.atom("BitVec"),
            solver.smt.numeral(16),
        ]),
    );
    solver.assume(solver.smt.eq(
        rev16ret,
        solver.smt.bvor(
            solver.smt.bvlshr(
                solver.smt.bvand(x3, solver.smt.atom("#xaaaa")),
                solver.smt.atom("#x0001"),
            ),
            solver.smt.bvshl(
                solver.smt.bvand(x3, solver.smt.atom("#x5555")),
                solver.smt.atom("#x0001"),
            ),
        ),
    ));

    let padding = solver.new_fresh_bits(solver.bitwidth - 16);
    solver.smt.concat(padding, rev16ret)
}

pub fn rev8(solver: &mut SolverCtx, x: SExpr, id: u32) -> SExpr {
    let x = solver.smt.extract(7, 0, x);

    // Generated code.
    let x1 = solver.declare(
        format!("x1_{id}", id = id),
        solver.smt.list(vec![
            solver.smt.atoms().und,
            solver.smt.atom("BitVec"),
            solver.smt.numeral(8),
        ]),
    );
    solver.assume(solver.smt.eq(
        x1,
        solver.smt.bvor(
            solver.smt.bvlshr(x, solver.smt.atom("#x04")),
            solver.smt.bvshl(x, solver.smt.atom("#x04")),
        ),
    ));
    let x2 = solver.declare(
        format!("x2_{id}", id = id),
        solver.smt.list(vec![
            solver.smt.atoms().und,
            solver.smt.atom("BitVec"),
            solver.smt.numeral(8),
        ]),
    );
    solver.assume(solver.smt.eq(
        x2,
        solver.smt.bvor(
            solver.smt.bvlshr(
                solver.smt.bvand(x1, solver.smt.atom("#xcc")),
                solver.smt.atom("#x02"),
            ),
            solver.smt.bvshl(
                solver.smt.bvand(x1, solver.smt.atom("#x33")),
                solver.smt.atom("#x02"),
            ),
        ),
    ));
    let rev8ret = solver.declare(
        format!("rev8ret_{id}", id = id),
        solver.smt.list(vec![
            solver.smt.atoms().und,
            solver.smt.atom("BitVec"),
            solver.smt.numeral(8),
        ]),
    );
    solver.assume(solver.smt.eq(
        rev8ret,
        solver.smt.bvor(
            solver.smt.bvlshr(
                solver.smt.bvand(x2, solver.smt.atom("#xaa")),
                solver.smt.atom("#x01"),
            ),
            solver.smt.bvshl(
                solver.smt.bvand(x2, solver.smt.atom("#x55")),
                solver.smt.atom("#x01"),
            ),
        ),
    ));

    let padding = solver.new_fresh_bits(solver.bitwidth - 8);
    solver.smt.concat(padding, rev8ret)
}

pub fn rev1(solver: &mut SolverCtx, x: SExpr, id: u32) -> SExpr {
    let x = solver.smt.extract(0, 0, x);

    // Generated code.
    let rev1ret = solver.declare(
        format!("rev1ret_{id}", id = id),
        solver.smt.list(vec![
            solver.smt.atoms().und,
            solver.smt.atom("BitVec"),
            solver.smt.numeral(1),
        ]),
    );
    solver.assume(solver.smt.eq(rev1ret, x));

    let padding = solver.new_fresh_bits(solver.bitwidth - 1);
    solver.smt.concat(padding, rev1ret)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::solver::SolverCtx;
    use std::collections::HashMap;
    use veri_ir::TypeContext;

    fn get_ctx() -> SolverCtx {
        let smt = easy_smt::ContextBuilder::new()
            .solver("z3", ["-smt2", "-in"])
            .build()
            .unwrap();
        SolverCtx {
            smt: smt,
            tyctx: TypeContext {
                tyvars: HashMap::new(),
                tymap: HashMap::new(),
                tyvals: HashMap::new(),
                bv_unknown_width_sets: HashMap::new(),
            },
            bitwidth: 64,
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
        check(
            &ctx,
            ctx.additional_assumptions[0],
            "(= rev1ret_42 ((_ extract 0 0) x))",
        );
    }

    fn check_rev_with_solver(input: &str, output: &str, width: usize) {
        let mut ctx = get_ctx();

        // Set up an input variable
        let ty = ctx.smt.bit_vec_sort(ctx.smt.numeral(width));
        let input_var = ctx.declare("input".to_string(), ty);

        // Set the input equal to our expected input
        ctx.additional_assumptions
            .push(ctx.smt.eq(input_var, ctx.smt.atom(input)));

        // Call the encoding function to be tested
        let output_from_rev = match width {
            1 => rev1(&mut ctx, input_var, 0),
            8 => rev8(&mut ctx, input_var, 0),
            16 => rev16(&mut ctx, input_var, 0),
            32 => rev32(&mut ctx, input_var, 0),
            64 => rev64(&mut ctx, input_var, 0),
            _ => unreachable!(),
        };

        // Extract the width of bits that we care about.
        let output_care_bits = ctx
            .smt
            .extract((width - 1).try_into().unwrap(), 0, output_from_rev);

        // Bookkeeping: declare declarations, assert assumptions
        for (name, ty) in &ctx.additional_decls {
            ctx.smt.declare_const(name, *ty).unwrap();
        }
        ctx.smt
            .assert(ctx.smt.and_many(ctx.additional_assumptions.clone()))
            .unwrap();

        // Check that our expected output is valid
        ctx.smt.push().unwrap();
        ctx.smt
            .assert(ctx.smt.eq(output_care_bits, ctx.smt.atom(output)))
            .unwrap();
        if !matches!(ctx.smt.check(), Ok(Response::Sat)) {
            // Bad! This is a bug!
            // Pop the output assertion
            ctx.smt.pop().unwrap();
            // Try again
            assert!(matches!(ctx.smt.check(), Ok(Response::Sat)));
            // Get the value for what output is to panic with a useful message
            let val = ctx.smt.get_value(vec![output_care_bits]).unwrap()[0].1;
            panic!("Expected {}, got {}", output, ctx.display_hex_to_bin(val));
        } else {
            ctx.smt.pop().unwrap();
        }

        // Check that there is no other possible output
        ctx.smt.push().unwrap();
        ctx.smt
            .assert(
                ctx.smt
                    .not(ctx.smt.eq(output_care_bits, ctx.smt.atom(output))),
            )
            .unwrap();
        assert!(matches!(ctx.smt.check(), Ok(Response::Unsat)));
        ctx.smt.pop().unwrap();
    }

    #[test]
    fn test_rev1_with_solver() {
        check_rev_with_solver("#b0", "#b0", 1);
        check_rev_with_solver("#b1", "#b1", 1);
    }

    #[test]
    fn test_rev8_with_solver() {
        check_rev_with_solver("#b01010101", "#b10101010", 8);
        check_rev_with_solver("#b11110000", "#b00001111", 8);
        check_rev_with_solver("#b00000000", "#b00000000", 8);
        check_rev_with_solver("#b11111111", "#b11111111", 8);
    }

    #[test]
    fn test_rev16_with_solver() {
        check_rev_with_solver("#b0101010101010101", "#b1010101010101010", 16);
        check_rev_with_solver("#b1111111100000000", "#b0000000011111111", 16);
        check_rev_with_solver("#b0000000000000000", "#b0000000000000000", 16);
        check_rev_with_solver("#b1111111111111111", "#b1111111111111111", 16);
    }

    #[test]
    fn test_rev32_with_solver() {
        check_rev_with_solver(
            "#b01010101010101010101010101010101",
            "#b10101010101010101010101010101010",
            32,
        );
        check_rev_with_solver(
            "#b11111111111111110000000000000000",
            "#b00000000000000001111111111111111",
            32,
        );
        check_rev_with_solver(
            "#b00000000000000000000000000000000",
            "#b00000000000000000000000000000000",
            32,
        );
        check_rev_with_solver(
            "#b11111111111111111111111111111111",
            "#b11111111111111111111111111111111",
            32,
        );
    }

    #[test]
    fn test_rev64_with_solver() {
        check_rev_with_solver(
            "#b0101010101010101010101010101010101010101010101010101010101010101",
            "#b1010101010101010101010101010101010101010101010101010101010101010",
            64,
        );
        check_rev_with_solver(
            "#b1111111111111111111111111111111100000000000000000000000000000000",
            "#b0000000000000000000000000000000011111111111111111111111111111111",
            64,
        );
        check_rev_with_solver(
            "#b0000000000000000000000000000000000000000000000000000000000000000",
            "#b0000000000000000000000000000000000000000000000000000000000000000",
            64,
        );
        check_rev_with_solver(
            "#b1111111111111111111111111111111111111111111111111111111111111111",
            "#b1111111111111111111111111111111111111111111111111111111111111111",
            64,
        );
    }
}
