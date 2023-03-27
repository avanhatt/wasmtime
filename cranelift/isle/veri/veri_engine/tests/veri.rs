mod utils;
use utils::{all_failure_result, all_success_result, custom_result, lte_64_success_result};
use utils::{
    run_and_retry, test_concrete_input_from_file_with_lhs_termname,
    test_from_file_with_lhs_termname, test_from_file_with_lhs_termname_dynwidth, Bitwidth,
};
use veri_ir::{ConcreteInput, ConcreteTest, Counterexample, VerificationResult};

#[test]
fn test_iadd_base_concrete() {
    run_and_retry(|| {
        test_concrete_input_from_file_with_lhs_termname(
            "./examples/iadd/base_case.isle",
            "iadd".to_string(),
            false,
            ConcreteTest {
                termname: "iadd".to_string(),
                args: vec![
                    ConcreteInput {
                        literal: "#b00000001".to_string(),
                        ty: veri_ir::Type::BitVector(Some(8)),
                    },
                    ConcreteInput {
                        literal: "#b00000001".to_string(),
                        ty: veri_ir::Type::BitVector(Some(8)),
                    },
                ],
                output: "#b00000010".to_string(),
            },
        )
    });
}

#[test]
fn test_iadd_base() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/iadd/base_case.isle",
            "iadd".to_string(),
            lte_64_success_result(),
        )
    });
}

#[test]
fn test_iadd_imm12() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/iadd/imm12.isle",
            "iadd".to_string(),
            lte_64_success_result(),
        )
    });
}

#[test]
fn test_iadd_imm12_2() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/iadd/imm12_2.isle",
            "iadd".to_string(),
            lte_64_success_result(),
        )
    });
}

#[test]
fn test_iadd_imm12neg_not_distinct() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/iadd/imm12neg.isle",
            "iadd".to_string(),
            vec![
                (Bitwidth::I8, VerificationResult::NoDistinctModels),
                (Bitwidth::I16, VerificationResult::NoDistinctModels),
                (Bitwidth::I32, VerificationResult::NoDistinctModels),
                (Bitwidth::I64, VerificationResult::Success),
            ],
        )
    });
}

#[test]
fn test_imm12_from_negated_value() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/iadd/imm12_from_negated_value.isle",
            "imm12_from_negated_value".to_string(),
            all_success_result(),
        )
    });
}

#[test]
fn test_iadd_imm12neg_new() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/iadd/imm12neg_new.isle",
            "iadd".to_string(),
            all_success_result(),
        )
    });
}

#[test]
fn test_iadd_imm12neg2_new() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/iadd/imm12neg2_new.isle",
            "iadd".to_string(),
            all_success_result(),
        )
    });
}

#[test]
fn test_iadd_imm12neg2_not_distinct() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/iadd/imm12neg2.isle",
            "iadd".to_string(),
            vec![
                (Bitwidth::I8, VerificationResult::NoDistinctModels),
                (Bitwidth::I16, VerificationResult::NoDistinctModels),
                (Bitwidth::I32, VerificationResult::NoDistinctModels),
                (Bitwidth::I64, VerificationResult::Success),
            ],
        )
    });
}

// Currently timing out, disabling for now.
// https://github.com/avanhatt/wasmtime/issues/13
// #[test]
// fn test_iadd_extend() {
//     run_and_retry(|| {
//         test_from_file_with_lhs_termname(
//             "./examples/iadd/extend.isle",
//             "iadd".to_string(),
//             lte_64_success_result(),
//         )
//     });
// }

// #[test]
// fn test_iadd_extend2() {
//     run_and_retry(|| {
//         test_from_file_with_lhs_termname(
//             "./examples/iadd/extend2.isle",
//             "iadd".to_string(),
//             lte_64_success_result(),
//         )
//     });
// }

#[test]
fn test_iadd_shift() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/iadd/shift.isle",
            "iadd".to_string(),
            lte_64_success_result(),
        )
    });
}

#[test]
fn test_iadd_madd() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/iadd/madd.isle",
            "iadd".to_string(),
            vec![
                (Bitwidth::I8, VerificationResult::Success),
                // Too slow right now: https://github.com/avanhatt/wasmtime/issues/36
                // (Bitwidth::I16, VerificationResult::Success),
                // (Bitwidth::I32, VerificationResult::Success),
                // (Bitwidth::I64, VerificationResult::Success),
            ],
        )
    });
}

#[test]
fn test_iadd_madd2() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/iadd/madd2.isle",
            "iadd".to_string(),
            vec![
                (Bitwidth::I8, VerificationResult::Success),
                // Too slow right now: https://github.com/avanhatt/wasmtime/issues/36
                // (Bitwidth::I16, VerificationResult::Success),
                // (Bitwidth::I32, VerificationResult::Success),
                // (Bitwidth::I64, VerificationResult::Success),
            ],
        )
    });
}

#[test]
fn test_isub_msub() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/isub/msub.isle",
            "isub".to_string(),
            vec![
                (Bitwidth::I8, VerificationResult::Success),
                // Too slow right now: https://github.com/avanhatt/wasmtime/issues/36
                // (Bitwidth::I16, VerificationResult::Success),
                // (Bitwidth::I32, VerificationResult::Success),
                // (Bitwidth::I64, VerificationResult::Success),
            ],
        )
    });
}

#[test]
fn test_broken_iadd_base_case() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/iadd/broken_base_case.isle",
            "iadd".to_string(),
            all_failure_result(),
        )
    });
}

#[test]
fn test_broken_iadd_imm12() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/iadd/broken_imm12.isle",
            "iadd".to_string(),
            vec![
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
}

#[test]
fn test_broken_iadd_imm12_2() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/iadd/broken_imm12_2.isle",
            "iadd".to_string(),
            vec![
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
}

#[test]
fn test_broken_iadd_imm12neg_not_distinct() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/iadd/broken_imm12neg.isle",
            "iadd".to_string(),
            vec![
                (Bitwidth::I8, VerificationResult::NoDistinctModels),
                (Bitwidth::I16, VerificationResult::NoDistinctModels),
                (Bitwidth::I32, VerificationResult::NoDistinctModels),
                (
                    Bitwidth::I64,
                    VerificationResult::Failure(Counterexample {}),
                ),
            ],
        )
    });
}

#[test]
fn test_broken_iadd_imm12neg_2_not_distinct() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/iadd/broken_imm12neg2.isle",
            "iadd".to_string(),
            vec![
                (Bitwidth::I8, VerificationResult::NoDistinctModels),
                (Bitwidth::I16, VerificationResult::NoDistinctModels),
                (Bitwidth::I32, VerificationResult::NoDistinctModels),
                (
                    Bitwidth::I64,
                    VerificationResult::Failure(Counterexample {}),
                ),
            ],
        )
    });
}

#[test]
fn test_broken_iadd_madd() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/iadd/broken_madd.isle",
            "iadd".to_string(),
            all_failure_result(),
        )
    });
}

#[test]
fn test_broken_iadd_madd2() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/iadd/broken_madd2.isle",
            "iadd".to_string(),
            all_failure_result(),
        )
    });
}

#[test]
fn test_broken_iadd_msub() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/iadd/broken_msub.isle",
            "isub".to_string(),
            vec![
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
}

#[test]
fn test_broken_iadd_shift() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/iadd/broken_shift.isle",
            "iadd".to_string(),
            all_failure_result(),
        )
    });
}

#[test]
fn test_broken_iadd_shift2() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/iadd/broken_shift2.isle",
            "iadd".to_string(),
            all_failure_result(),
        )
    });
}

#[test]
fn test_isub_base_case() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/isub/base_case.isle",
            "isub".to_string(),
            lte_64_success_result(),
        )
    })
}

#[test]
fn test_isub_imm12() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/isub/imm12.isle",
            "isub".to_string(),
            lte_64_success_result(),
        )
    })
}

#[test]
fn test_isub_imm12_concrete() {
    run_and_retry(|| {
        test_concrete_input_from_file_with_lhs_termname(
            "./examples/isub/imm12.isle",
            "isub".to_string(),
            false,
            ConcreteTest {
                termname: "isub".to_string(),
                args: vec![
                    ConcreteInput {
                        literal: "#b00000001".to_string(),
                        ty: veri_ir::Type::BitVector(Some(8)),
                    },
                    ConcreteInput {
                        literal: "#b11111111".to_string(),
                        ty: veri_ir::Type::BitVector(Some(8)),
                    },
                ],
                output: "#b00000010".to_string(),
            },
        )
    });
}

#[test]
fn test_isub_imm12neg_not_distinct() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/isub/imm12neg.isle",
            "isub".to_string(),
            vec![
                (Bitwidth::I8, VerificationResult::NoDistinctModels),
                (Bitwidth::I16, VerificationResult::NoDistinctModels),
                (Bitwidth::I32, VerificationResult::NoDistinctModels),
                (Bitwidth::I64, VerificationResult::Success),
            ],
        );
    })
}

#[test]
fn test_isub_imm12neg_new() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/isub/imm12neg_new.isle",
            "isub".to_string(),
            all_success_result(),
        );
    })
}

#[test]
fn test_isub_imm12neg_concrete32() {
    run_and_retry(|| {
        test_concrete_input_from_file_with_lhs_termname(
            "./examples/isub/imm12neg.isle",
            "isub".to_string(),
            false,
            ConcreteTest {
                termname: "isub".to_string(),
                args: vec![
                    ConcreteInput {
                        literal:
                            "#b0000000000000000000000000000000000000000000000000000000000000001"
                                .to_string(),
                        ty: veri_ir::Type::BitVector(Some(64)),
                    },
                    ConcreteInput {
                        literal:
                            "#b1111111111111111111111111111111111111111111111111111111111111111"
                                .to_string(),
                        ty: veri_ir::Type::BitVector(Some(64)),
                    },
                ],
                output: "#b0000000000000000000000000000000000000000000000000000000000000010"
                    .to_string(),
            },
        )
    });
}

#[test]
fn test_isub_imm12neg_concrete_64() {
    run_and_retry(|| {
        test_concrete_input_from_file_with_lhs_termname(
            "./examples/isub/imm12neg.isle",
            "isub".to_string(),
            false,
            ConcreteTest {
                termname: "isub".to_string(),
                args: vec![
                    ConcreteInput {
                        literal:
                            "#b0000000000000000000000000000000000000000000000000000000000000001"
                                .to_string(),
                        ty: veri_ir::Type::BitVector(Some(64)),
                    },
                    ConcreteInput {
                        literal:
                            "#b1111111111111111111111111111111111111111111111111111111111111111"
                                .to_string(),
                        ty: veri_ir::Type::BitVector(Some(64)),
                    },
                ],
                output: "#b0000000000000000000000000000000000000000000000000000000000000010"
                    .to_string(),
            },
        )
    });
}

#[test]
fn test_isub_extend() {
    run_and_retry(|| {
        //test_from_file_with_lhs_termname("./examples/isub/extend.isle", lte_64_success_result());
    })
}

#[test]
fn test_isub_shift() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/isub/shift.isle",
            "isub".to_string(),
            lte_64_success_result(),
        );
    })
}

#[test]
fn test_broken_isub_base_case() {
    test_from_file_with_lhs_termname(
        "./examples/broken/isub/broken_base_case.isle",
        "isub".to_string(),
        vec![
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
}

#[test]
fn test_broken_isub_imm12() {
    test_from_file_with_lhs_termname(
        "./examples/broken/isub/broken_imm12.isle",
        "isub".to_string(),
        vec![
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
}

#[test]
fn test_broken_isub_imm12neg_not_distinct() {
    test_from_file_with_lhs_termname(
        "./examples/broken/isub/broken_imm12neg.isle",
        "isub".to_string(),
        vec![
            (Bitwidth::I8, VerificationResult::NoDistinctModels),
            (Bitwidth::I16, VerificationResult::NoDistinctModels),
            (Bitwidth::I32, VerificationResult::NoDistinctModels),
            (
                Bitwidth::I64,
                VerificationResult::Failure(Counterexample {}),
            ),
        ],
    );
}

#[test]
fn test_broken_isub_shift() {
    test_from_file_with_lhs_termname(
        "./examples/broken/isub/broken_shift.isle",
        "isub".to_string(),
        all_failure_result(),
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
            // Too slow right now: https://github.com/avanhatt/wasmtime/issues/36
            vec![
                (Bitwidth::I8, VerificationResult::Success),
                // (Bitwidth::I16, VerificationResult::Success),
                // (Bitwidth::I32, VerificationResult::Success),
                // (Bitwidth::I64, VerificationResult::Success),
            ],
        )
    });
}

#[test]
fn test_udiv() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/udiv/udiv.isle",
            "udiv".to_string(),
            // Too slow right now: https://github.com/avanhatt/wasmtime/issues/36
            vec![
                (Bitwidth::I8, VerificationResult::Success),
                // (Bitwidth::I16, VerificationResult::Success),
                // (Bitwidth::I32, VerificationResult::Success),
                // (Bitwidth::I64, VerificationResult::Success),
            ],
        )
    })
}

#[test]
fn test_broken_udiv() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/udiv/broken_udiv.isle",
            "udiv".to_string(),
            vec![
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
    })
}

#[test]
fn test_sdiv() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/sdiv/sdiv.isle",
            "sdiv".to_string(),
            vec![
                (Bitwidth::I8, VerificationResult::Success),
                // Too slow right now: https://github.com/avanhatt/wasmtime/issues/36
                // (Bitwidth::I16, VerificationResult::Success),
                // (Bitwidth::I32, VerificationResult::Success),
                // (Bitwidth::I64, VerificationResult::Success),
            ],
        )
    })
}

#[test]
fn test_sdiv_safe_const() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/sdiv/sdiv_safe_const.isle",
            "sdiv".to_string(),
            vec![
                (Bitwidth::I8, VerificationResult::Success),
                // Too slow right now: https://github.com/avanhatt/wasmtime/issues/36
                // (Bitwidth::I16, VerificationResult::Success),
                // (Bitwidth::I32, VerificationResult::Success),
                // (Bitwidth::I64, VerificationResult::Success),
            ],
        )
    })
}

#[test]
fn test_broken_sdiv_safe_const() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/sdiv/broken_sdiv_safe_const.isle",
            "sdiv".to_string(),
            vec![
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
}

#[test]
fn test_broken_sdiv() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/sdiv/broken_sdiv.isle",
            "sdiv".to_string(),
            vec![
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
    })
}

#[test]
fn test_srem() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/srem/srem.isle",
            "srem".to_string(),
            vec![
                (Bitwidth::I8, VerificationResult::Success),
                // Too slow right now: https://github.com/avanhatt/wasmtime/issues/36
                // (Bitwidth::I16, VerificationResult::Success),
                // (Bitwidth::I32, VerificationResult::Success),
                // (Bitwidth::I64, VerificationResult::Success),
            ],
        )
    })
}

#[test]
fn test_srem_concrete() {
    run_and_retry(|| {
        test_concrete_input_from_file_with_lhs_termname(
            "./examples/srem/srem.isle",
            "srem".to_string(),
            false,
            ConcreteTest {
                termname: "srem".to_string(),
                args: vec![
                    ConcreteInput {
                        literal: "#b11111110".to_string(),
                        ty: veri_ir::Type::BitVector(Some(8)),
                    },
                    ConcreteInput {
                        literal: "#b00110001".to_string(),
                        ty: veri_ir::Type::BitVector(Some(8)),
                    },
                ],
                output: "#b11111110".to_string(),
            },
        )
    });
}

#[test]
fn test_urem() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/urem/urem.isle",
            "urem".to_string(),
            vec![
                (Bitwidth::I8, VerificationResult::Success),
                // Too slow right now: https://github.com/avanhatt/wasmtime/issues/36
                // (Bitwidth::I16, VerificationResult::Success),
                // (Bitwidth::I32, VerificationResult::Success),
                // (Bitwidth::I64, VerificationResult::Success),
            ],
        )
    })
}

#[test]
fn test_urem_concrete() {
    run_and_retry(|| {
        test_concrete_input_from_file_with_lhs_termname(
            "./examples/urem/urem.isle",
            "urem".to_string(),
            false,
            ConcreteTest {
                termname: "urem".to_string(),
                args: vec![
                    ConcreteInput {
                        literal: "#b11111110".to_string(),
                        ty: veri_ir::Type::BitVector(Some(8)),
                    },
                    ConcreteInput {
                        literal: "#b00110001".to_string(),
                        ty: veri_ir::Type::BitVector(Some(8)),
                    },
                ],
                output: "#b00001001".to_string(),
            },
        )
    });
}

#[test]
fn test_uextend() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname_dynwidth(
            "./examples/uextend/uextend.isle",
            "uextend".to_string(),
            all_success_result(),
        )
    })
}

#[test]
fn test_sextend() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname_dynwidth(
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
        test_from_file_with_lhs_termname_dynwidth(
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
                (Bitwidth::I8, VerificationResult::InapplicableRule),
                (Bitwidth::I16, VerificationResult::InapplicableRule),
                (Bitwidth::I32, VerificationResult::Success),
                (Bitwidth::I64, VerificationResult::Success),
            ],
        )
    });
}

#[test]
fn test_clz8() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/clz/clz8.isle",
            "clz".to_string(),
            vec![
                (Bitwidth::I8, VerificationResult::Success),
                (Bitwidth::I16, VerificationResult::InapplicableRule),
                (Bitwidth::I32, VerificationResult::InapplicableRule),
                (Bitwidth::I64, VerificationResult::InapplicableRule),
            ],
        )
    });
}

#[test]
fn test_clz16() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/clz/clz16.isle",
            "clz".to_string(),
            vec![
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
}

#[test]
fn test_clz8_broken() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/clz/broken_clz8.isle",
            "clz".to_string(),
            vec![
                (Bitwidth::I8, VerificationResult::Failure(Counterexample {})),
                (Bitwidth::I16, VerificationResult::InapplicableRule),
                (Bitwidth::I32, VerificationResult::InapplicableRule),
                (Bitwidth::I64, VerificationResult::InapplicableRule),
            ],
        )
    });
}

#[test]
fn test_clz_broken16() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/clz/broken_clz16.isle",
            "clz".to_string(),
            vec![
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
                (Bitwidth::I8, VerificationResult::InapplicableRule),
                (Bitwidth::I16, VerificationResult::InapplicableRule),
                (Bitwidth::I32, VerificationResult::Success),
                (Bitwidth::I64, VerificationResult::Success),
            ],
        )
    });
}

#[test]
fn test_cls8() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/cls/cls8.isle",
            "cls".to_string(),
            vec![
                (Bitwidth::I8, VerificationResult::Success),
                (Bitwidth::I16, VerificationResult::InapplicableRule),
                (Bitwidth::I32, VerificationResult::InapplicableRule),
                (Bitwidth::I64, VerificationResult::InapplicableRule),
            ],
        )
    });
}

#[test]
fn test_cls16() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/cls/cls16.isle",
            "cls".to_string(),
            vec![
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
}

#[test]
fn test_cls8_broken() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/cls/broken_cls8.isle",
            "cls".to_string(),
            vec![
                (Bitwidth::I8, VerificationResult::Failure(Counterexample {})),
                (Bitwidth::I16, VerificationResult::InapplicableRule),
                (Bitwidth::I32, VerificationResult::InapplicableRule),
                (Bitwidth::I64, VerificationResult::InapplicableRule),
            ],
        )
    });
}

#[test]
fn test_cls16_broken() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/cls/broken_cls16.isle",
            "cls".to_string(),
            vec![
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
                (Bitwidth::I8, VerificationResult::InapplicableRule),
                (Bitwidth::I16, VerificationResult::InapplicableRule),
                (Bitwidth::I32, VerificationResult::Success),
                (Bitwidth::I64, VerificationResult::Success),
            ],
        )
    });
}

#[test]
fn test_ctz8() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/ctz/ctz8.isle",
            "ctz".to_string(),
            vec![
                (Bitwidth::I8, VerificationResult::Success),
                (Bitwidth::I16, VerificationResult::InapplicableRule),
                (Bitwidth::I32, VerificationResult::InapplicableRule),
                (Bitwidth::I64, VerificationResult::InapplicableRule),
            ],
        )
    });
}

#[test]
fn test_ctz16() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/ctz/ctz16.isle",
            "ctz".to_string(),
            vec![
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
            "clz".to_string(),
            vec![
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
}

#[test]
fn test_ctz8_broken() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/ctz/broken_ctz8.isle",
            "ctz".to_string(),
            vec![
                (Bitwidth::I8, VerificationResult::Failure(Counterexample {})),
                (Bitwidth::I16, VerificationResult::InapplicableRule),
                (Bitwidth::I32, VerificationResult::InapplicableRule),
                (Bitwidth::I64, VerificationResult::InapplicableRule),
            ],
        )
    });
}

#[test]
fn test_ctz16_broken() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/ctz/broken_ctz16.isle",
            "ctz".to_string(),
            vec![
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
}

#[test]
fn test_small_rotr_to_shifts_broken2() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/broken_rule_or_small_rotr.isle",
            "small_rotr".to_string(),
            vec![
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
                (Bitwidth::I8, VerificationResult::InapplicableRule),
                (Bitwidth::I16, VerificationResult::InapplicableRule),
                (Bitwidth::I32, VerificationResult::Success),
                (Bitwidth::I64, VerificationResult::InapplicableRule),
            ],
        )
    })
}

#[test]
fn test_broken_fits_in_16_with_imm_rotl_to_rotr() {
    test_from_file_with_lhs_termname(
        "./examples/broken/broken_fits_in_16_with_imm_rotl_to_rotr.isle",
        "rotl".to_string(),
        vec![
            (Bitwidth::I8, VerificationResult::Failure(Counterexample {})),
            (
                Bitwidth::I16,
                VerificationResult::Failure(Counterexample {}),
            ),
            (Bitwidth::I32, VerificationResult::InapplicableRule),
            (Bitwidth::I64, VerificationResult::InapplicableRule),
        ],
    )
}

#[test]
fn test_fits_in_16_rotr() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/rotr/fits_in_16_rotr.isle",
            "rotr".to_string(),
            vec![
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
                (Bitwidth::I8, VerificationResult::InapplicableRule),
                (Bitwidth::I16, VerificationResult::InapplicableRule),
                (Bitwidth::I32, VerificationResult::Success),
                (Bitwidth::I64, VerificationResult::InapplicableRule),
            ],
        )
    })
}

#[test]
fn test_64_rotr() {
    test_from_file_with_lhs_termname(
        "./examples/rotr/64_rotr.isle",
        "rotr".to_string(),
        vec![
            (Bitwidth::I8, VerificationResult::InapplicableRule),
            (Bitwidth::I16, VerificationResult::InapplicableRule),
            (Bitwidth::I32, VerificationResult::InapplicableRule),
            (Bitwidth::I64, VerificationResult::Success),
        ],
    )
}

#[test]
fn test_64_with_imm_rotr() {
    test_from_file_with_lhs_termname(
        "./examples/rotr/64_with_imm_rotr.isle",
        "rotr".to_string(),
        vec![
            (Bitwidth::I8, VerificationResult::InapplicableRule),
            (Bitwidth::I16, VerificationResult::InapplicableRule),
            (Bitwidth::I32, VerificationResult::InapplicableRule),
            (Bitwidth::I64, VerificationResult::Success),
        ],
    )
}

#[test]
fn test_fits_in_32_band() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/band/fits_in_32_band.isle",
            "band".to_string(),
            vec![
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
                (Bitwidth::I8, VerificationResult::InapplicableRule),
                (Bitwidth::I16, VerificationResult::InapplicableRule),
                (Bitwidth::I32, VerificationResult::InapplicableRule),
                (Bitwidth::I64, VerificationResult::Success),
            ],
        )
    })
}

#[test]
fn test_ishl_to_do_shift_64() {
    test_from_file_with_lhs_termname(
        "./examples/shifts/ishl_to_do_shift_64.isle",
        "ishl".to_string(),
        vec![
            (Bitwidth::I8, VerificationResult::InapplicableRule),
            (Bitwidth::I16, VerificationResult::InapplicableRule),
            (Bitwidth::I32, VerificationResult::InapplicableRule),
            (Bitwidth::I64, VerificationResult::Success),
        ],
    )
}

#[test]
fn test_ishl_to_do_shift_64_concrete() {
    run_and_retry(|| {
        test_concrete_input_from_file_with_lhs_termname(
            "./examples/shifts/ishl_to_do_shift_64.isle",
            "ishl".to_string(),
            false,
            ConcreteTest {
                termname: "ishl".to_string(),
                args: vec![
                    ConcreteInput {
                        literal:
                            "#b0000000000000000000000000000000000000000000000000000000000000001"
                                .to_string(),
                        ty: veri_ir::Type::BitVector(Some(64)),
                    },
                    ConcreteInput {
                        literal:
                            "#b0000000000000000000000000000000000000000000000000000000000000010"
                                .to_string(),
                        ty: veri_ir::Type::BitVector(Some(64)),
                    },
                ],
                output: "#b0000000000000000000000000000000000000000000000000000000000000100"
                    .to_string(),
            },
        )
    });
}

#[test]
fn test_ishl_to_do_shift_fits_in_32() {
    test_from_file_with_lhs_termname(
        "./examples/shifts/ishl_to_do_shift_fits_in_32.isle",
        "ishl".to_string(),
        vec![
            (Bitwidth::I8, VerificationResult::Success),
            (Bitwidth::I16, VerificationResult::Success),
            (Bitwidth::I32, VerificationResult::Success),
            (Bitwidth::I64, VerificationResult::InapplicableRule),
        ],
    )
}

#[test]
fn test_ishl_to_do_shift_fits_in_32_concrete() {
    run_and_retry(|| {
        test_concrete_input_from_file_with_lhs_termname(
            "./examples/shifts/ishl_to_do_shift_fits_in_32.isle",
            "ishl".to_string(),
            false,
            ConcreteTest {
                termname: "ishl".to_string(),
                args: vec![
                    ConcreteInput {
                        literal: "#b00000001".to_string(),
                        ty: veri_ir::Type::BitVector(Some(8)),
                    },
                    ConcreteInput {
                        literal: "#b00000010".to_string(),
                        ty: veri_ir::Type::BitVector(Some(8)),
                    },
                ],
                output: "#b00000100".to_string(),
            },
        )
    });
}

#[test]
fn test_sshr_to_do_shift_64() {
    test_from_file_with_lhs_termname(
        "./examples/shifts/sshr_to_do_shift_64.isle",
        "sshr".to_string(),
        vec![
            (Bitwidth::I8, VerificationResult::InapplicableRule),
            (Bitwidth::I16, VerificationResult::InapplicableRule),
            (Bitwidth::I32, VerificationResult::InapplicableRule),
            (Bitwidth::I64, VerificationResult::Success),
        ],
    )
}

#[test]
fn test_sshr_to_do_shift_fits_in_32() {
    test_from_file_with_lhs_termname(
        "./examples/shifts/sshr_to_do_shift_fits_in_32.isle",
        "sshr".to_string(),
        vec![
            (Bitwidth::I8, VerificationResult::Success),
            (Bitwidth::I16, VerificationResult::Success),
            (Bitwidth::I32, VerificationResult::Success),
            (Bitwidth::I64, VerificationResult::InapplicableRule),
        ],
    )
}

#[test]
fn test_sshr_to_do_shift_fits_in_32_concrete() {
    test_concrete_input_from_file_with_lhs_termname(
        "./examples/shifts/sshr_to_do_shift_fits_in_32.isle",
        "sshr".to_string(),
        false,
        ConcreteTest {
            termname: "sshr".to_string(),
            args: vec![
                ConcreteInput {
                    literal: "#b10100000".to_string(),
                    ty: veri_ir::Type::BitVector(Some(8)),
                },
                ConcreteInput {
                    literal: "#b00000001".to_string(),
                    ty: veri_ir::Type::BitVector(Some(8)),
                },
            ],
            output: "#b11010000".to_string(),
        },
    )
}

#[test]
fn test_ushr_to_do_shift_64() {
    test_from_file_with_lhs_termname(
        "./examples/shifts/ushr_to_do_shift_64.isle",
        "ushr".to_string(),
        vec![
            (Bitwidth::I8, VerificationResult::InapplicableRule),
            (Bitwidth::I16, VerificationResult::InapplicableRule),
            (Bitwidth::I32, VerificationResult::InapplicableRule),
            (Bitwidth::I64, VerificationResult::Success),
        ],
    )
}

#[test]
fn test_ushr_to_do_shift_fits_in_32() {
    test_from_file_with_lhs_termname(
        "./examples/shifts/ushr_to_do_shift_fits_in_32.isle",
        "ushr".to_string(),
        vec![
            (Bitwidth::I8, VerificationResult::Success),
            (Bitwidth::I16, VerificationResult::Success),
            (Bitwidth::I32, VerificationResult::Success),
            (Bitwidth::I64, VerificationResult::InapplicableRule),
        ],
    )
}

#[test]
fn test_ushr_to_do_shift_fits_in_32_concrete() {
    test_concrete_input_from_file_with_lhs_termname(
        "./examples/shifts/ushr_to_do_shift_fits_in_32.isle",
        "ushr".to_string(),
        false,
        ConcreteTest {
            termname: "ushr".to_string(),
            args: vec![
                ConcreteInput {
                    literal: "#b10100000".to_string(),
                    ty: veri_ir::Type::BitVector(Some(8)),
                },
                ConcreteInput {
                    literal: "#b00000001".to_string(),
                    ty: veri_ir::Type::BitVector(Some(8)),
                },
            ],
            output: "#b01010000".to_string(),
        },
    )
}

#[test]
fn test_do_shift_with_imm() {
    test_from_file_with_lhs_termname(
        "./examples/shifts/do_shift_with_imm.isle",
        "do_shift".to_string(),
        vec![
            (Bitwidth::I8, VerificationResult::Success),
            (Bitwidth::I16, VerificationResult::Success),
            (Bitwidth::I32, VerificationResult::Success),
            (Bitwidth::I64, VerificationResult::Success),
        ],
    )
}

#[test]
fn test_do_shift_fits_in_16() {
    test_from_file_with_lhs_termname(
        "./examples/shifts/do_shift_fits_in_16.isle",
        "do_shift".to_string(),
        vec![
            (Bitwidth::I8, VerificationResult::Success),
            (Bitwidth::I16, VerificationResult::Success),
            (Bitwidth::I32, VerificationResult::InapplicableRule),
            (Bitwidth::I64, VerificationResult::InapplicableRule),
        ],
    )
}

#[test]
fn test_do_shift_32() {
    test_from_file_with_lhs_termname(
        "./examples/shifts/do_shift_32.isle",
        "do_shift".to_string(),
        vec![
            (Bitwidth::I8, VerificationResult::InapplicableRule),
            (Bitwidth::I16, VerificationResult::InapplicableRule),
            (Bitwidth::I32, VerificationResult::Success),
            (Bitwidth::I64, VerificationResult::InapplicableRule),
        ],
    )
}

#[test]
fn test_broken_do_shift_32() {
    test_from_file_with_lhs_termname(
        "./examples/broken/shifts/broken_do_shift_32.isle",
        "do_shift".to_string(),
        vec![
            (Bitwidth::I8, VerificationResult::InapplicableRule),
            (Bitwidth::I16, VerificationResult::InapplicableRule),
            (
                Bitwidth::I32,
                VerificationResult::Failure(Counterexample {}),
            ),
            (Bitwidth::I64, VerificationResult::InapplicableRule),
        ],
    )
}

#[test]
fn test_broken_ishl_to_do_shift_64() {
    test_from_file_with_lhs_termname(
        "./examples/broken/shifts/broken_ishl_to_do_shift_64.isle",
        "ishl".to_string(),
        vec![
            (Bitwidth::I8, VerificationResult::InapplicableRule),
            (Bitwidth::I16, VerificationResult::InapplicableRule),
            (Bitwidth::I32, VerificationResult::InapplicableRule),
            (
                Bitwidth::I64,
                VerificationResult::Failure(Counterexample {}),
            ),
        ],
    )
}

#[test]
fn test_broken_sshr_to_do_shift_fits_in_32() {
    test_from_file_with_lhs_termname(
        "./examples/broken/shifts/broken_sshr_to_do_shift_fits_in_32.isle",
        "sshr".to_string(),
        vec![
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
}

#[test]
fn test_broken_sshr_to_do_shift_fits_in_32_concrete() {
    test_concrete_input_from_file_with_lhs_termname(
        "./examples/broken/shifts/broken_sshr_to_do_shift_fits_in_32.isle",
        "sshr".to_string(),
        false,
        ConcreteTest {
            termname: "sshr".to_string(),
            args: vec![
                ConcreteInput {
                    literal: "#b10100000".to_string(),
                    ty: veri_ir::Type::BitVector(Some(8)),
                },
                ConcreteInput {
                    literal: "#b00000001".to_string(),
                    ty: veri_ir::Type::BitVector(Some(8)),
                },
            ],
            // Wrong output:
            output: "#b01010000".to_string(),
        },
    )
}

#[test]
fn test_broken_ushr_to_do_shift_fits_in_32() {
    test_from_file_with_lhs_termname(
        "./examples/broken/shifts/broken_ushr_to_do_shift_fits_in_32.isle",
        "ushr".to_string(),
        vec![
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
}

#[test]
fn test_do_shift_64() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/shifts/do_shift_64.isle",
            "do_shift".to_string(),
            vec![
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
