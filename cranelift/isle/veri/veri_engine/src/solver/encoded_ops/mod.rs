pub mod cls;
pub mod clz;
pub mod rev;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::solver::SolverCtx;
    use easy_smt::{Response, SExpr};
    use std::collections::HashMap;
    use veri_ir::TypeContext;

    fn get_ctx() -> SolverCtx {
        let smt = easy_smt::ContextBuilder::new()
            .solver("z3", ["-smt2", "-in"])
            .build()
            .unwrap();
        SolverCtx {
            smt: smt,
            dynwidths: true,
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

    /// Check that the solver encoding meets expectations for the given input and output.
    /// Right now, only works for encodings with a single argument that return a value with
    /// the same width as the input.
    /// Check that the output is equal to the expected output, and no other output is possible.
    fn check_encoding_with_solver(encoding: &str, input: &str, output: &str, width: usize) {
        let mut ctx = get_ctx();

        // Set up an input variable
        let ty = ctx.smt.bit_vec_sort(ctx.smt.numeral(width));
        let input_var = ctx.declare("input".to_string(), ty);

        // Set the input equal to our expected input
        ctx.additional_assumptions
            .push(ctx.smt.eq(input_var, ctx.smt.atom(input)));

        // Call the encoding function to be tested
        let output_from_call = match (encoding, width) {
            ("rev", 1) => rev::rev1(&mut ctx, input_var, 0),
            ("rev", 8) => rev::rev8(&mut ctx, input_var, 0),
            ("rev", 16) => rev::rev16(&mut ctx, input_var, 0),
            ("rev", 32) => rev::rev32(&mut ctx, input_var, 0),
            ("rev", 64) => rev::rev64(&mut ctx, input_var, 0),

            ("clz", 1) => clz::clz1(&mut ctx, input_var, 0),
            ("clz", 8) => clz::clz8(&mut ctx, input_var, 0),
            ("clz", 16) => clz::clz16(&mut ctx, input_var, 0),
            ("clz", 32) => clz::clz32(&mut ctx, input_var, 0),
            ("clz", 64) => clz::clz64(&mut ctx, input_var, 0),

            ("cls", 1) => cls::cls1(&mut ctx, 0),
            ("cls", 8) => cls::cls8(&mut ctx, input_var, 0),
            ("cls", 16) => cls::cls16(&mut ctx, input_var, 0),
            ("cls", 32) => cls::cls32(&mut ctx, input_var, 0),
            ("cls", 64) => cls::cls64(&mut ctx, input_var, 0),
            _ => unreachable!(),
        };

        // Extract the width of bits that we care about.
        let output_care_bits =
            ctx.smt
                .extract((width - 1).try_into().unwrap(), 0, output_from_call);

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

    fn check(ctx: &SolverCtx, expr: SExpr, expected: &str) {
        let expr_s = format!("{}", ctx.smt.display(expr));
        assert_eq!(expr_s, expected);
    }

    #[test]
    fn rev1_test() {
        let mut ctx = get_ctx();

        let x = ctx.smt.atom("x");
        let res = rev::rev1(&mut ctx, x, 42);

        check(&ctx, res, "(concat fresh0 rev1ret_42)");
        check(&ctx, ctx.additional_decls[0].1, "(_ BitVec 1)");
        check(
            &ctx,
            ctx.additional_assumptions[0],
            "(= rev1ret_42 ((_ extract 0 0) x))",
        );
    }

    #[test]
    fn test_rev1_with_solver() {
        check_encoding_with_solver("rev", "#b0", "#b0", 1);
        check_encoding_with_solver("rev", "#b1", "#b1", 1);
    }

    #[test]
    fn test_rev8_with_solver() {
        check_encoding_with_solver("rev", "#b01010101", "#b10101010", 8);
        check_encoding_with_solver("rev", "#b11110000", "#b00001111", 8);
        check_encoding_with_solver("rev", "#b00000000", "#b00000000", 8);
        check_encoding_with_solver("rev", "#b11111111", "#b11111111", 8);
    }

    #[test]
    fn test_rev16_with_solver() {
        check_encoding_with_solver("rev", "#b0101010101010101", "#b1010101010101010", 16);
        check_encoding_with_solver("rev", "#b1111111100000000", "#b0000000011111111", 16);
        check_encoding_with_solver("rev", "#b0000000000000000", "#b0000000000000000", 16);
        check_encoding_with_solver("rev", "#b1111111111111111", "#b1111111111111111", 16);
    }

    #[test]
    fn test_rev32_with_solver() {
        check_encoding_with_solver(
            "rev",
            "#b01010101010101010101010101010101",
            "#b10101010101010101010101010101010",
            32,
        );
        check_encoding_with_solver(
            "rev",
            "#b11111111111111110000000000000000",
            "#b00000000000000001111111111111111",
            32,
        );
        check_encoding_with_solver(
            "rev",
            "#b00000000000000000000000000000000",
            "#b00000000000000000000000000000000",
            32,
        );
        check_encoding_with_solver(
            "rev",
            "#b11111111111111111111111111111111",
            "#b11111111111111111111111111111111",
            32,
        );
    }

    #[test]
    fn test_rev64_with_solver() {
        check_encoding_with_solver(
            "rev",
            "#b0101010101010101010101010101010101010101010101010101010101010101",
            "#b1010101010101010101010101010101010101010101010101010101010101010",
            64,
        );
        check_encoding_with_solver(
            "rev",
            "#b1111111111111111111111111111111100000000000000000000000000000000",
            "#b0000000000000000000000000000000011111111111111111111111111111111",
            64,
        );
        check_encoding_with_solver(
            "rev",
            "#b0000000000000000000000000000000000000000000000000000000000000000",
            "#b0000000000000000000000000000000000000000000000000000000000000000",
            64,
        );
        check_encoding_with_solver(
            "rev",
            "#b1111111111111111111111111111111111111111111111111111111111111111",
            "#b1111111111111111111111111111111111111111111111111111111111111111",
            64,
        );
    }

    #[test]
    fn test_clz1_with_solver() {
        check_encoding_with_solver("clz", "#b0", "#b1", 1);
        check_encoding_with_solver("clz", "#b1", "#b0", 1);
    }

    #[test]
    fn test_clz8_with_solver() {
        check_encoding_with_solver("clz", "#b00000000", "#b00001000", 8);
        check_encoding_with_solver("clz", "#b01111111", "#b00000001", 8);
        check_encoding_with_solver("clz", "#b11111111", "#b00000000", 8);
    }

    #[test]
    fn test_clz16_with_solver() {
        check_encoding_with_solver("clz", "#b0000000000000000", "#b0000000000010000", 16);
        check_encoding_with_solver("clz", "#b0000000000000001", "#b0000000000001111", 16);
        check_encoding_with_solver("clz", "#b0111111111111111", "#b0000000000000001", 16);
        check_encoding_with_solver("clz", "#b1111111111111111", "#b0000000000000000", 16);
    }

    #[test]
    fn test_clz32_with_solver() {
        check_encoding_with_solver(
            "clz",
            "#b00000000000000000000000000000000",
            "#b00000000000000000000000000100000",
            32,
        );
        check_encoding_with_solver(
            "clz",
            "#b00000000000000000000000000000001",
            "#b00000000000000000000000000011111",
            32,
        );
        check_encoding_with_solver(
            "clz",
            "#b01000000000000000000000000000000",
            "#b00000000000000000000000000000001",
            32,
        );
        check_encoding_with_solver(
            "clz",
            "#b11111111111111111111111111111111",
            "#b00000000000000000000000000000000",
            32,
        );
    }

    #[test]
    fn test_clz64_with_solver() {
        check_encoding_with_solver(
            "clz",
            "#b0000000000000000000000000000000000000000000000000000000000000000",
            "#b0000000000000000000000000000000000000000000000000000000001000000",
            64,
        );
        check_encoding_with_solver(
            "clz",
            "#b0000000000000000000000000000000000000000000000000000000000000001",
            "#b0000000000000000000000000000000000000000000000000000000000111111",
            64,
        );
        check_encoding_with_solver(
            "clz",
            "#b0100000000000000000000000000000000000000000000000000000000000000",
            "#b0000000000000000000000000000000000000000000000000000000000000001",
            64,
        );
        check_encoding_with_solver(
            "clz",
            "#b1111111111111111111111111111111111111111111111111111111111111111",
            "#b0000000000000000000000000000000000000000000000000000000000000000",
            64,
        );
    }

    #[test]
    fn test_cls1_with_solver() {
        check_encoding_with_solver("cls", "#b0", "#b0", 1);
        check_encoding_with_solver("cls", "#b1", "#b0", 1);
    }

    #[test]
    fn test_cls8_with_solver() {
        check_encoding_with_solver("cls", "#b00000000", "#b00000111", 8);
        check_encoding_with_solver("cls", "#b01111111", "#b00000000", 8);
        check_encoding_with_solver("cls", "#b00111111", "#b00000001", 8);
        check_encoding_with_solver("cls", "#b11000000", "#b00000001", 8);
        check_encoding_with_solver("cls", "#b11111111", "#b00000111", 8);
    }

    #[test]
    fn test_cls16_with_solver() {
        check_encoding_with_solver("cls", "#b0000000000000000", "#b0000000000001111", 16);
        check_encoding_with_solver("cls", "#b0111111111111111", "#b0000000000000000", 16);
        check_encoding_with_solver("cls", "#b0011111111111111", "#b0000000000000001", 16);
        check_encoding_with_solver("cls", "#b1111111111111111", "#b0000000000001111", 16);
    }

    #[test]
    fn test_cls32_with_solver() {
        check_encoding_with_solver(
            "cls",
            "#b00000000000000000000000000000000",
            "#b00000000000000000000000000011111",
            32,
        );
        check_encoding_with_solver(
            "cls",
            "#b01111111111111111111111111111111",
            "#b00000000000000000000000000000000",
            32,
        );
        check_encoding_with_solver(
            "cls",
            "#b00100000000000000000000000000000",
            "#b00000000000000000000000000000001",
            32,
        );
        check_encoding_with_solver(
            "cls",
            "#b11111111111111111111111111111111",
            "#b00000000000000000000000000011111",
            32,
        );
    }

    #[test]
    fn test_cls64_with_solver() {
        check_encoding_with_solver(
            "cls",
            "#b0000000000000000000000000000000000000000000000000000000000000000",
            "#b0000000000000000000000000000000000000000000000000000000000111111",
            64,
        );
        check_encoding_with_solver(
            "cls",
            "#b0010000000000000000000000000000000000000000000000000000000000000",
            "#b0000000000000000000000000000000000000000000000000000000000000001",
            64,
        );
        check_encoding_with_solver(
            "cls",
            "#b0111111111111111111111111111111111111111111111111111111111111111",
            "#b0000000000000000000000000000000000000000000000000000000000000000",
            64,
        );
        check_encoding_with_solver(
            "cls",
            "#b1111111111111111111111111111111111111111111111111111111111111111",
            "#b0000000000000000000000000000000000000000000000000000000000111111",
            64,
        );
    }
}
