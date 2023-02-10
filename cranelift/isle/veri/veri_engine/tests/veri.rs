mod utils;
use utils::{
    all_failure_result, all_success_result, custom_result, just_8_result, lte_64_success_result,
};
use utils::{run_and_retry, test_from_file_with_lhs_termname, Bitwidth};
use veri_ir::{Counterexample, VerificationResult};

// #[test]
// fn test_iadds() {
/*test_from_file_custom_prelude(
    "./tests/code/selfcontained/simple_prelude.isle",
    "./tests/code/selfcontained/simple_iadd.isle",
    lte_64_success_result(),
);

test_from_file_custom_prelude(
    "./tests/code/selfcontained/simple_prelude.isle",
    "./tests/code/selfcontained/iadd_to_sub.isle",
    lte_64_success_result(),
);*/
// }

#[test]
fn test_implicit_conversions() {
    // test_from_file_custom_prelude(
    //     "./tests/code/selfcontained/prelude.isle",
    //     "./tests/code/selfcontained/simple_iadd_implicit_conv.isle",
    //     lte_64_success_result(),
    // );

    /*
    test_from_file_custom_prelude(
        "./tests/code/selfcontained/prelude.isle",
        "./tests/code/selfcontained/iadd_to_sub_implicit_conv.isle",
        lte_64_success_result()
    );
    */
}

// Currently timing out, disabling for now.
// https://github.com/avanhatt/wasmtime/issues/13
/*
#[test]
fn test_iadd_base() {
    run_and_retry(|| test_from_file_with_lhs_termname("./examples/iadd/base_case.isle", lte_64_success_result()));
}

#[test]
fn test_iadd_imm12() {
    run_and_retry(|| test_from_file_with_lhs_termname("./examples/iadd/imm12.isle", lte_64_success_result()));
}

#[test]
fn test_iadd_imm12_2() {
    run_and_retry(|| test_from_file_with_lhs_termname("./examples/iadd/imm12_2.isle", lte_64_success_result()));
}

#[test]
fn test_iadd_imm12neg() {
    run_and_retry(|| test_from_file_with_lhs_termname("./examples/iadd/imm12neg.isle", lte_64_success_result()));
}

#[test]
fn test_iadd_imm12neg2() {
    run_and_retry(|| test_from_file_with_lhs_termname("./examples/iadd/imm12neg2.isle", lte_64_success_result()));
}

// Currently timing out, disabling for now.
// https://github.com/avanhatt/wasmtime/issues/13
// #[test]
// fn test_iadd_extend() {
//test_from_file_with_lhs_termname("./examples/iadd/extend.isle", lte_64_success_result());
//test_from_file_with_lhs_termname("./examples/iadd/extend2.isle", lte_64_success_result());
// }

#[test]
fn test_iadd_shift() {
    run_and_retry(|| test_from_file_with_lhs_termname("./examples/iadd/shift.isle", lte_64_success_result()));
}

#[test]
fn test_iadd_madd() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/iadd/madd.isle",
            vec![
                (Bitwidth::I1, VerificationResult::Success),
                (Bitwidth::I8, VerificationResult::Success),
                (Bitwidth::I16, VerificationResult::Success),
                (Bitwidth::I32, VerificationResult::Success),
                (Bitwidth::I64, VerificationResult::Success),
            ],
        )
    });
}

#[test]
fn test_iadd_madd2() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/iadd/madd2.isle",
            vec![
                (Bitwidth::I1, VerificationResult::Success),
                (Bitwidth::I8, VerificationResult::Success),
                (Bitwidth::I16, VerificationResult::Success),
                (Bitwidth::I32, VerificationResult::Success),
                (Bitwidth::I64, VerificationResult::Success),
            ],
        )
    });
}

#[test]
fn test_iadd_msub() {
    run_and_retry(|| test_from_file_with_lhs_termname("./examples/iadd/msub.isle", lte_64_success_result()));
}
*/

#[test]
fn test_broken_iadd_from_file() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/iadd/broken_base_case.isle",
            "iadd".to_string(),
            all_failure_result(),
        )
    });
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/iadd/broken_imm12.isle",
            "iadd".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::Success),
                (Bitwidth::I8, VerificationResult::Failure(Counterexample {})),
                (
                    Bitwidth::I16,
                    VerificationResult::Failure(Counterexample {}),
                ),
                (
                    Bitwidth::I32,
                    VerificationResult::Failure(Counterexample {}),
                ),
                (
                    Bitwidth::I64,
                    VerificationResult::Failure(Counterexample {}),
                ),
            ],
        )
    });
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/iadd/broken_imm12_2.isle",
            "iadd".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::Success),
                (Bitwidth::I8, VerificationResult::Failure(Counterexample {})),
                (
                    Bitwidth::I16,
                    VerificationResult::Failure(Counterexample {}),
                ),
                (
                    Bitwidth::I32,
                    VerificationResult::Failure(Counterexample {}),
                ),
                (
                    Bitwidth::I64,
                    VerificationResult::Failure(Counterexample {}),
                ),
            ],
        )
    });
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/iadd/broken_imm12neg.isle",
            "iadd".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::Success),
                (Bitwidth::I8, VerificationResult::Failure(Counterexample {})),
                (
                    Bitwidth::I16,
                    VerificationResult::Failure(Counterexample {}),
                ),
                (
                    Bitwidth::I32,
                    VerificationResult::Failure(Counterexample {}),
                ),
                (
                    Bitwidth::I64,
                    VerificationResult::Failure(Counterexample {}),
                ),
            ],
        )
    });
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/iadd/broken_imm12neg2.isle",
            "iadd".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::Success),
                (Bitwidth::I8, VerificationResult::Failure(Counterexample {})),
                (
                    Bitwidth::I16,
                    VerificationResult::Failure(Counterexample {}),
                ),
                (
                    Bitwidth::I32,
                    VerificationResult::Failure(Counterexample {}),
                ),
                (
                    Bitwidth::I64,
                    VerificationResult::Failure(Counterexample {}),
                ),
            ],
        )
    });
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/iadd/broken_madd.isle",
            "iadd".to_string(),
            all_failure_result(),
        )
    });
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/iadd/broken_madd2.isle",
            "iadd".to_string(),
            all_failure_result(),
        )
    });
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/iadd/broken_msub.isle",
            "iadd".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::Success),
                (Bitwidth::I8, VerificationResult::Failure(Counterexample {})),
                (
                    Bitwidth::I16,
                    VerificationResult::Failure(Counterexample {}),
                ),
                (
                    Bitwidth::I32,
                    VerificationResult::Failure(Counterexample {}),
                ),
                (
                    Bitwidth::I64,
                    VerificationResult::Failure(Counterexample {}),
                ),
            ],
        )
    });
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/iadd/broken_shift.isle",
            "iadd".to_string(),
            all_failure_result(),
        )
    });
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/iadd/broken_shift2.isle",
            "iadd".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::InapplicableRule),
                (Bitwidth::I8, VerificationResult::InapplicableRule),
                (Bitwidth::I16, VerificationResult::InapplicableRule),
                (Bitwidth::I32, VerificationResult::InapplicableRule),
                (Bitwidth::I64, VerificationResult::InapplicableRule),
            ],
        )
    });
}

#[test]
fn test_isub_from_file() {
    test_from_file_with_lhs_termname(
        "./examples/isub/base_case.isle",
        "isub".to_string(),
        lte_64_success_result(),
    );
    test_from_file_with_lhs_termname(
        "./examples/isub/imm12.isle",
        "isub".to_string(),
        lte_64_success_result(),
    );
    test_from_file_with_lhs_termname(
        "./examples/isub/imm12neg.isle",
        "isub".to_string(),
        lte_64_success_result(),
    );
    //test_from_file_with_lhs_termname("./examples/isub/extend.isle", lte_64_success_result());
    test_from_file_with_lhs_termname(
        "./examples/isub/shift.isle",
        "isub".to_string(),
        lte_64_success_result(),
    );
}

#[test]
fn test_broken_isub_from_file() {
    test_from_file_with_lhs_termname(
        "./examples/broken/isub/broken_base_case.isle",
        "isub".to_string(),
        vec![
            (Bitwidth::I1, VerificationResult::Success),
            (Bitwidth::I8, VerificationResult::Failure(Counterexample {})),
            (
                Bitwidth::I16,
                VerificationResult::Failure(Counterexample {}),
            ),
            (
                Bitwidth::I32,
                VerificationResult::Failure(Counterexample {}),
            ),
            (
                Bitwidth::I64,
                VerificationResult::Failure(Counterexample {}),
            ),
        ],
    );
    test_from_file_with_lhs_termname(
        "./examples/broken/isub/broken_imm12.isle",
        "isub".to_string(),
        vec![
            (Bitwidth::I1, VerificationResult::Success),
            (Bitwidth::I8, VerificationResult::Failure(Counterexample {})),
            (
                Bitwidth::I16,
                VerificationResult::Failure(Counterexample {}),
            ),
            (
                Bitwidth::I32,
                VerificationResult::Failure(Counterexample {}),
            ),
            (
                Bitwidth::I64,
                VerificationResult::Failure(Counterexample {}),
            ),
        ],
    );
    test_from_file_with_lhs_termname(
        "./examples/broken/isub/broken_imm12neg.isle",
        "isub".to_string(),
        vec![
            (Bitwidth::I1, VerificationResult::Success),
            (Bitwidth::I8, VerificationResult::Failure(Counterexample {})),
            (
                Bitwidth::I16,
                VerificationResult::Failure(Counterexample {}),
            ),
            (
                Bitwidth::I32,
                VerificationResult::Failure(Counterexample {}),
            ),
            (
                Bitwidth::I64,
                VerificationResult::Failure(Counterexample {}),
            ),
        ],
    );

    test_from_file_with_lhs_termname(
        "./examples/broken/iadd/broken_shift.isle",
        "isub".to_string(),
        all_failure_result(),
    );
    test_from_file_with_lhs_termname(
        "./examples/broken/iadd/broken_shift2.isle",
        "isub".to_string(),
        vec![
            (Bitwidth::I1, VerificationResult::InapplicableRule),
            (Bitwidth::I8, VerificationResult::InapplicableRule),
            (Bitwidth::I16, VerificationResult::InapplicableRule),
            (Bitwidth::I32, VerificationResult::InapplicableRule),
            (Bitwidth::I64, VerificationResult::InapplicableRule),
        ],
    );
}

#[test]
fn test_ineg() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/ineg/ineg.isle",
            "ineg".to_string(),
            lte_64_success_result(),
        )
    })
}

#[test]
fn test_mul() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/imul/imul.isle",
            "imul".to_string(),
            lte_64_success_result(),
        )
    });
}

/*
#[test]
fn test_udiv() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/udiv/udiv.isle",
            // for ease of commenting out until we debug further
            vec![
                (Bitwidth::I1, VerificationResult::Success),
                (Bitwidth::I8, VerificationResult::Success),
                // (Bitwidth::I16, VerificationResult::Success),
                // (Bitwidth::I32, VerificationResult::Success),
                (Bitwidth::I64, VerificationResult::Success),
            ],
        )
    })
}
*/

#[test]
fn test_uextend() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/uextend/uextend.isle",
            "uextend".to_string(),
            all_success_result(),
        )
    })
}

#[test]
fn test_sextend() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/sextend/sextend.isle",
            "sextend".to_string(),
            all_success_result(),
        )
    })
}

#[test]
fn test_broken_uextend() {
    // In the spec for extend, zero_extend and sign_extend are swapped.
    // However, this should still work in the case where the query with
    // is the same as the register width (64).
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/broken_uextend.isle",
            "uextend".to_string(),
            custom_result(&|w| {
                (
                    w,
                    if (w as usize) < 64 {
                        VerificationResult::Failure(Counterexample {})
                    } else {
                        VerificationResult::Success
                    },
                )
            }),
        )
    })
}

#[test]
fn test_clz() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/clz/clz.isle",
            "clz".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::InapplicableRule),
                (Bitwidth::I8, VerificationResult::InapplicableRule),
                (Bitwidth::I16, VerificationResult::InapplicableRule),
                (Bitwidth::I32, VerificationResult::Success),
                (Bitwidth::I64, VerificationResult::Success),
            ],
        )
    });

    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/clz/clz8.isle",
            "clz".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::InapplicableRule),
                (Bitwidth::I8, VerificationResult::Success),
                (Bitwidth::I16, VerificationResult::InapplicableRule),
                (Bitwidth::I32, VerificationResult::InapplicableRule),
                (Bitwidth::I64, VerificationResult::InapplicableRule),
            ],
        )
    });

    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/clz/clz16.isle",
            "clz".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::InapplicableRule),
                (Bitwidth::I8, VerificationResult::InapplicableRule),
                (Bitwidth::I16, VerificationResult::Success),
                (Bitwidth::I32, VerificationResult::InapplicableRule),
                (Bitwidth::I64, VerificationResult::InapplicableRule),
            ],
        )
    })
}

#[test]
fn test_clz_broken() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/clz/broken_clz.isle",
            "clz".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::Failure(Counterexample {})),
                (Bitwidth::I8, VerificationResult::Failure(Counterexample {})),
                (
                    Bitwidth::I16,
                    VerificationResult::Failure(Counterexample {}),
                ),
                (
                    Bitwidth::I32,
                    VerificationResult::Failure(Counterexample {}),
                ),
                (Bitwidth::I64, VerificationResult::Success),
            ],
        )
    });

    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/clz/broken_clz8.isle",
            "clz".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::InapplicableRule),
                (Bitwidth::I8, VerificationResult::Failure(Counterexample {})),
                (Bitwidth::I16, VerificationResult::InapplicableRule),
                (Bitwidth::I32, VerificationResult::InapplicableRule),
                (Bitwidth::I64, VerificationResult::InapplicableRule),
            ],
        )
    });

    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/clz/broken_clz16.isle",
            "clz".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::InapplicableRule),
                (Bitwidth::I8, VerificationResult::InapplicableRule),
                (
                    Bitwidth::I16,
                    VerificationResult::Failure(Counterexample {}),
                ),
                (Bitwidth::I32, VerificationResult::InapplicableRule),
                (Bitwidth::I64, VerificationResult::InapplicableRule),
            ],
        )
    })
}

#[test]
fn test_cls() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/cls/cls.isle",
            "cls".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::InapplicableRule),
                (Bitwidth::I8, VerificationResult::InapplicableRule),
                (Bitwidth::I16, VerificationResult::InapplicableRule),
                (Bitwidth::I32, VerificationResult::Success),
                (Bitwidth::I64, VerificationResult::Success),
            ],
        )
    });

    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/cls/cls8.isle",
            "cls".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::InapplicableRule),
                (Bitwidth::I8, VerificationResult::Success),
                (Bitwidth::I16, VerificationResult::InapplicableRule),
                (Bitwidth::I32, VerificationResult::InapplicableRule),
                (Bitwidth::I64, VerificationResult::InapplicableRule),
            ],
        )
    });

    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/cls/cls16.isle",
            "cls".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::InapplicableRule),
                (Bitwidth::I8, VerificationResult::InapplicableRule),
                (Bitwidth::I16, VerificationResult::Success),
                (Bitwidth::I32, VerificationResult::InapplicableRule),
                (Bitwidth::I64, VerificationResult::InapplicableRule),
            ],
        )
    })
}

#[test]
fn test_cls_broken() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/cls/broken_cls.isle",
            "cls".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::Failure(Counterexample {})),
                (Bitwidth::I8, VerificationResult::Failure(Counterexample {})),
                (
                    Bitwidth::I16,
                    VerificationResult::Failure(Counterexample {}),
                ),
                (Bitwidth::I32, VerificationResult::Success),
                (Bitwidth::I64, VerificationResult::Success),
            ],
        )
    });

    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/cls/broken_cls8.isle",
            "cls".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::InapplicableRule),
                (Bitwidth::I8, VerificationResult::Failure(Counterexample {})),
                (Bitwidth::I16, VerificationResult::InapplicableRule),
                (Bitwidth::I32, VerificationResult::InapplicableRule),
                (Bitwidth::I64, VerificationResult::InapplicableRule),
            ],
        )
    });

    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/cls/broken_cls16.isle",
            "cls".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::InapplicableRule),
                (Bitwidth::I8, VerificationResult::InapplicableRule),
                (
                    Bitwidth::I16,
                    VerificationResult::Failure(Counterexample {}),
                ),
                (Bitwidth::I32, VerificationResult::InapplicableRule),
                (Bitwidth::I64, VerificationResult::InapplicableRule),
            ],
        )
    })
}

#[test]
fn test_ctz() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/ctz/ctz.isle",
            "ctz".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::InapplicableRule),
                (Bitwidth::I8, VerificationResult::InapplicableRule),
                (Bitwidth::I16, VerificationResult::InapplicableRule),
                (Bitwidth::I32, VerificationResult::Success),
                (Bitwidth::I64, VerificationResult::Success),
            ],
        )
    });

    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/ctz/ctz8.isle",
            "ctz".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::InapplicableRule),
                (Bitwidth::I8, VerificationResult::Success),
                (Bitwidth::I16, VerificationResult::InapplicableRule),
                (Bitwidth::I32, VerificationResult::InapplicableRule),
                (Bitwidth::I64, VerificationResult::InapplicableRule),
            ],
        )
    });

    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/ctz/ctz16.isle",
            "ctz".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::InapplicableRule),
                (Bitwidth::I8, VerificationResult::InapplicableRule),
                (Bitwidth::I16, VerificationResult::Success),
                (Bitwidth::I32, VerificationResult::InapplicableRule),
                (Bitwidth::I64, VerificationResult::InapplicableRule),
            ],
        )
    })
}

#[test]
fn test_ctz_broken() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/ctz/broken_ctz.isle",
            "ctz".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::InapplicableRule),
                (Bitwidth::I8, VerificationResult::InapplicableRule),
                (Bitwidth::I16, VerificationResult::InapplicableRule),
                (
                    Bitwidth::I32,
                    VerificationResult::Failure(Counterexample {}),
                ),
                (
                    Bitwidth::I64,
                    VerificationResult::Failure(Counterexample {}),
                ),
            ],
        )
    });

    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/ctz/broken_ctz8.isle",
            "ctz".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::InapplicableRule),
                (Bitwidth::I8, VerificationResult::Failure(Counterexample {})),
                (Bitwidth::I16, VerificationResult::InapplicableRule),
                (Bitwidth::I32, VerificationResult::InapplicableRule),
                (Bitwidth::I64, VerificationResult::InapplicableRule),
            ],
        )
    });

    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/ctz/broken_ctz16.isle",
            "ctz".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::InapplicableRule),
                (Bitwidth::I8, VerificationResult::InapplicableRule),
                (
                    Bitwidth::I16,
                    VerificationResult::Failure(Counterexample {}),
                ),
                (Bitwidth::I32, VerificationResult::InapplicableRule),
                (Bitwidth::I64, VerificationResult::InapplicableRule),
            ],
        )
    })
}

#[test]
fn test_small_rotr_to_shifts() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/rotr/small_rotr_to_shifts.isle",
            "small_rotr".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::Success),
                (Bitwidth::I8, VerificationResult::Success),
                (Bitwidth::I16, VerificationResult::Success),
                (Bitwidth::I32, VerificationResult::InapplicableRule),
                (Bitwidth::I64, VerificationResult::InapplicableRule),
            ],
        )
    })
}

#[test]
fn test_small_rotr_to_shifts_broken() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/broken_mask_small_rotr.isle",
            "small_rotr".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::Success),
                (Bitwidth::I8, VerificationResult::Failure(Counterexample {})),
                (
                    Bitwidth::I16,
                    VerificationResult::Failure(Counterexample {}),
                ),
                (Bitwidth::I32, VerificationResult::InapplicableRule),
                (Bitwidth::I64, VerificationResult::InapplicableRule),
            ],
        )
    });
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/broken_rule_or_small_rotr.isle",
            "small_rotr".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::Failure(Counterexample {})),
                (Bitwidth::I8, VerificationResult::Failure(Counterexample {})),
                (
                    Bitwidth::I16,
                    VerificationResult::Failure(Counterexample {}),
                ),
                (Bitwidth::I32, VerificationResult::InapplicableRule),
                (Bitwidth::I64, VerificationResult::InapplicableRule),
            ],
        )
    })
}

#[test]
fn test_small_rotr_imm_to_shifts() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/rotr/small_rotr_imm_to_shifts.isle",
            "small_rotr_imm".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::Success),
                (Bitwidth::I8, VerificationResult::Success),
                (Bitwidth::I16, VerificationResult::Success),
                (Bitwidth::I32, VerificationResult::InapplicableRule),
                (Bitwidth::I64, VerificationResult::InapplicableRule),
            ],
        )
    })
}

#[test]
fn test_fits_in_16_rotl_to_rotr() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/rotl/fits_in_16_rotl_to_rotr.isle",
            "rotl".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::Success),
                (Bitwidth::I8, VerificationResult::Success),
                (Bitwidth::I16, VerificationResult::Success),
                (Bitwidth::I32, VerificationResult::InapplicableRule),
                (Bitwidth::I64, VerificationResult::InapplicableRule),
            ],
        )
    })
}

#[test]
fn test_32_general_rotl_to_rotr() {
    run_and_retry(|| {
        run_and_retry(|| {
            test_from_file_with_lhs_termname(
                "./examples/rotl/32_general_rotl_to_rotr.isle",
                "rotl".to_string(),
                vec![
                    (Bitwidth::I1, VerificationResult::InapplicableRule),
                    (Bitwidth::I8, VerificationResult::InapplicableRule),
                    (Bitwidth::I16, VerificationResult::InapplicableRule),
                    (Bitwidth::I32, VerificationResult::Success),
                    (Bitwidth::I64, VerificationResult::InapplicableRule),
                ],
            )
        })
    })
}

#[test]
fn test_broken_32_general_rotl_to_rotr() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/broken_32_general_rotl_to_rotr.isle",
            "rotl".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::InapplicableRule),
                (Bitwidth::I8, VerificationResult::InapplicableRule),
                (Bitwidth::I16, VerificationResult::InapplicableRule),
                (
                    Bitwidth::I32,
                    VerificationResult::Failure(Counterexample {}),
                ),
                (Bitwidth::I64, VerificationResult::InapplicableRule),
            ],
        )
    })
}

#[test]
fn test_64_general_rotl_to_rotr() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/rotl/64_general_rotl_to_rotr.isle",
            "rotl".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::InapplicableRule),
                (Bitwidth::I8, VerificationResult::InapplicableRule),
                (Bitwidth::I16, VerificationResult::InapplicableRule),
                (Bitwidth::I32, VerificationResult::InapplicableRule),
                (Bitwidth::I64, VerificationResult::Success),
            ],
        )
    })
}

#[test]
fn test_broken_fits_in_16_rotl_to_rotr() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/broken_fits_in_16_rotl_to_rotr.isle",
            "rotl".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::Success),
                (Bitwidth::I8, VerificationResult::Failure(Counterexample {})),
                (
                    Bitwidth::I16,
                    VerificationResult::Failure(Counterexample {}),
                ),
                (Bitwidth::I32, VerificationResult::InapplicableRule),
                (Bitwidth::I64, VerificationResult::InapplicableRule),
            ],
        )
    })
}

#[test]
fn test_fits_in_16_with_imm_rotl_to_rotr() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/rotl/fits_in_16_with_imm_rotl_to_rotr.isle",
            "rotl".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::Success),
                (Bitwidth::I8, VerificationResult::Success),
                (Bitwidth::I16, VerificationResult::Success),
                (Bitwidth::I32, VerificationResult::InapplicableRule),
                (Bitwidth::I64, VerificationResult::InapplicableRule),
            ],
        )
    })
}

#[test]
fn test_64_with_imm_rotl_to_rotr() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/rotl/64_with_imm_rotl_to_rotr.isle",
            "rotl".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::InapplicableRule),
                (Bitwidth::I8, VerificationResult::InapplicableRule),
                (Bitwidth::I16, VerificationResult::InapplicableRule),
                (Bitwidth::I32, VerificationResult::InapplicableRule),
                (Bitwidth::I64, VerificationResult::Success),
            ],
        )
    })
}

#[test]
fn test_32_with_imm_rotl_to_rotr() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/rotl/32_with_imm_rotl_to_rotr.isle",
            "rotl".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::InapplicableRule),
                (Bitwidth::I8, VerificationResult::InapplicableRule),
                (Bitwidth::I16, VerificationResult::InapplicableRule),
                (Bitwidth::I32, VerificationResult::Success),
                (Bitwidth::I64, VerificationResult::InapplicableRule),
            ],
        )
    })
}

// #[test]
// fn test_broken_fits_in_16_with_imm_rotl_to_rotr() {
//     test_from_file_with_lhs_termname(
//         "./examples/broken/broken_fits_in_16_with_imm_rotl_to_rotr.isle",
//         "rotl".to_string(),
//         vec![
//             (Bitwidth::I1, VerificationResult::Success),
//             (Bitwidth::I8, VerificationResult::Failure(Counterexample {})),
//             (
//                 Bitwidth::I16,
//                 VerificationResult::Failure(Counterexample {}),
//             ),
//             (Bitwidth::I32, VerificationResult::InapplicableRule),
//             (Bitwidth::I64, VerificationResult::InapplicableRule),
//         ],
//     )
// }

#[test]
fn test_fits_in_16_rotr() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/rotr/fits_in_16_rotr.isle",
            "rotr".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::Success),
                (Bitwidth::I8, VerificationResult::Success),
                (Bitwidth::I16, VerificationResult::Success),
                (Bitwidth::I32, VerificationResult::InapplicableRule),
                (Bitwidth::I64, VerificationResult::InapplicableRule),
            ],
        )
    })
}

#[test]
fn test_fits_in_16_with_imm_rotr() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/rotr/fits_in_16_rotr.isle",
            "rotr".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::Success),
                (Bitwidth::I8, VerificationResult::Success),
                (Bitwidth::I16, VerificationResult::Success),
                (Bitwidth::I32, VerificationResult::InapplicableRule),
                (Bitwidth::I64, VerificationResult::InapplicableRule),
            ],
        )
    })
}

#[test]
fn test_32_rotr() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/rotr/32_rotr.isle",
            "rotr".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::InapplicableRule),
                (Bitwidth::I8, VerificationResult::InapplicableRule),
                (Bitwidth::I16, VerificationResult::InapplicableRule),
                (Bitwidth::I32, VerificationResult::Success),
                (Bitwidth::I64, VerificationResult::InapplicableRule),
            ],
        )
    })
}

#[test]
fn test_32_with_imm_rotr() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/rotr/32_with_imm_rotr.isle",
            "rotr".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::InapplicableRule),
                (Bitwidth::I8, VerificationResult::InapplicableRule),
                (Bitwidth::I16, VerificationResult::InapplicableRule),
                (Bitwidth::I32, VerificationResult::Success),
                (Bitwidth::I64, VerificationResult::InapplicableRule),
            ],
        )
    })
}

// TODO: reenable.
// #[test]
// fn test_64_rotr() {
//     test_from_file_with_lhs_termname(
//         "./examples/64_rotr.isle",
//         "rotr".to_string(),
//         vec![
//             (Bitwidth::I1, VerificationResult::InapplicableRule),
//             (Bitwidth::I8, VerificationResult::InapplicableRule),
//             (Bitwidth::I16, VerificationResult::InapplicableRule),
//             (Bitwidth::I32, VerificationResult::InapplicableRule),
//             (Bitwidth::I64, VerificationResult::Success),
//         ],
//     )
// }

// Test timing out, reenable with
// https://github.com/avanhatt/wasmtime/issues/14
// #[test]
// fn test_64_with_imm_rotr() {
//     test_from_file_with_lhs_termname(
//         "./examples/64_with_imm_rotr.isle",
//         "rotr".to_string(),
//         vec![
//             (Bitwidth::I1, VerificationResult::InapplicableRule),
//             (Bitwidth::I8, VerificationResult::InapplicableRule),
//             (Bitwidth::I16, VerificationResult::InapplicableRule),
//             (Bitwidth::I32, VerificationResult::InapplicableRule),
//             (Bitwidth::I64, VerificationResult::Success),
//         ],
//     )
// }

#[test]
fn test_fits_in_32_band() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/band/fits_in_32_band.isle",
            "band".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::Success),
                (Bitwidth::I8, VerificationResult::Success),
                (Bitwidth::I16, VerificationResult::Success),
                (Bitwidth::I32, VerificationResult::Success),
                (Bitwidth::I64, VerificationResult::InapplicableRule),
            ],
        )
    })
}

#[test]
fn test_broken_fits_in_32_band() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/broken_fits_in_32_band.isle",
            "band".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::Failure(Counterexample {})),
                (Bitwidth::I8, VerificationResult::Failure(Counterexample {})),
                (
                    Bitwidth::I16,
                    VerificationResult::Failure(Counterexample {}),
                ),
                (
                    Bitwidth::I32,
                    VerificationResult::Failure(Counterexample {}),
                ),
                (Bitwidth::I64, VerificationResult::InapplicableRule),
            ],
        )
    })
}

#[test]
fn test_64_band() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/band/64_band.isle",
            "band".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::InapplicableRule),
                (Bitwidth::I8, VerificationResult::InapplicableRule),
                (Bitwidth::I16, VerificationResult::InapplicableRule),
                (Bitwidth::I32, VerificationResult::InapplicableRule),
                (Bitwidth::I64, VerificationResult::Success),
            ],
        )
    })
}

#[test]
fn test_fits_in_32_bor() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/bor/fits_in_32_bor.isle",
            "bor".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::Success),
                (Bitwidth::I8, VerificationResult::Success),
                (Bitwidth::I16, VerificationResult::Success),
                (Bitwidth::I32, VerificationResult::Success),
                (Bitwidth::I64, VerificationResult::InapplicableRule),
            ],
        )
    })
}

#[test]
fn test_64_bor() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/bor/64_bor.isle",
            "bor".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::InapplicableRule),
                (Bitwidth::I8, VerificationResult::InapplicableRule),
                (Bitwidth::I16, VerificationResult::InapplicableRule),
                (Bitwidth::I32, VerificationResult::InapplicableRule),
                (Bitwidth::I64, VerificationResult::Success),
            ],
        )
    })
}

#[test]
fn test_broken_fits_in_32_bor() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/broken_fits_in_32_bor.isle",
            "bor".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::Failure(Counterexample {})),
                (Bitwidth::I8, VerificationResult::Failure(Counterexample {})),
                (
                    Bitwidth::I16,
                    VerificationResult::Failure(Counterexample {}),
                ),
                (
                    Bitwidth::I32,
                    VerificationResult::Failure(Counterexample {}),
                ),
                (Bitwidth::I64, VerificationResult::InapplicableRule),
            ],
        )
    })
}

#[test]
fn test_fits_in_32_bxor() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/bxor/fits_in_32_bxor.isle",
            "bxor".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::Success),
                (Bitwidth::I8, VerificationResult::Success),
                (Bitwidth::I16, VerificationResult::Success),
                (Bitwidth::I32, VerificationResult::Success),
                (Bitwidth::I64, VerificationResult::InapplicableRule),
            ],
        )
    })
}

#[test]
fn test_64_bxor() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/bxor/64_bxor.isle",
            "bxor".to_string(),
            vec![
                (Bitwidth::I1, VerificationResult::InapplicableRule),
                (Bitwidth::I8, VerificationResult::InapplicableRule),
                (Bitwidth::I16, VerificationResult::InapplicableRule),
                (Bitwidth::I32, VerificationResult::InapplicableRule),
                (Bitwidth::I64, VerificationResult::Success),
            ],
        )
    })
}

#[test]
fn test_if_let() {
    test_from_file_with_lhs_termname(
        "./examples/constructs/if-let.isle",
        "iadd".to_string(),
        all_success_result(),
    );
}

#[test]
fn test_let() {
    // test_from_file_self_contained("./tests/code/selfcontained/let.isle", just_8_result());
}
