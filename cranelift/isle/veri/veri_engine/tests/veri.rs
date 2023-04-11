mod utils;
use utils::{all_failure_result, all_success_result, custom_result, lte_64_success_result};
use utils::{
    run_and_retry, test_aarch64_rule_with_lhs_termname, test_aarch64_with_config,
    test_concrete_aarch64_rule_with_lhs_termname, test_concrete_input_from_file_with_lhs_termname,
    test_from_file_with_config, test_from_file_with_lhs_termname,
    test_from_file_with_lhs_termname_dynwidth, Bitwidth,
};
use veri_engine_lib::Config;
use veri_ir::{ConcreteInput, ConcreteTest, Counterexample, VerificationResult};

#[test]
fn test_named_iadd_base_concrete() {
    run_and_retry(|| {
        test_concrete_aarch64_rule_with_lhs_termname(
            "iadd_base_case",
            "iadd",
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
                output: ConcreteInput {
                    literal: "#b00000010".to_string(),
                    ty: veri_ir::Type::BitVector(Some(8)),
                },
            },
        )
    });
}

#[test]
fn test_named_iadd_base() {
    run_and_retry(|| {
        test_aarch64_rule_with_lhs_termname("iadd_base_case", "iadd", lte_64_success_result())
    });
}

#[test]
fn test_named_iadd_imm12_right() {
    run_and_retry(|| {
        test_aarch64_rule_with_lhs_termname("iadd_imm12_right", "iadd", lte_64_success_result())
    });
}

#[test]
fn test_named_iadd_imm12_left() {
    run_and_retry(|| {
        test_aarch64_rule_with_lhs_termname("iadd_imm12_left", "iadd", lte_64_success_result())
    });
}

#[test]
fn test_named_iadd_imm12_neg_left() {
    run_and_retry(|| {
        test_aarch64_rule_with_lhs_termname(
            "iadd_imm12_neg_left",
            "iadd",
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
fn test_named_iadd_imm12_neg_right_not_distinct() {
    run_and_retry(|| {
        test_aarch64_rule_with_lhs_termname(
            "iadd_imm12_neg_right",
            "iadd",
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
fn test_named_iadd_imm12_neg_left_not_distinct() {
    run_and_retry(|| {
        test_aarch64_rule_with_lhs_termname(
            "iadd_imm12_neg_left",
            "iadd",
            vec![
                (Bitwidth::I8, VerificationResult::NoDistinctModels),
                (Bitwidth::I16, VerificationResult::NoDistinctModels),
                (Bitwidth::I32, VerificationResult::NoDistinctModels),
                (Bitwidth::I64, VerificationResult::Success),
            ],
        )
    });
}

// Need a file test because this is a change on top of our latest rebase
#[test]
fn test_imm12_from_negated_value() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/iadd/imm12_from_negated_value_new.isle",
            "imm12_from_negated_value".to_string(),
            all_success_result(),
        )
    });
}

// Need a file test because this is a change on top of our latest rebase
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

// Need a file test because this is a change on top of our latest rebase
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
fn test_named_iadd_extend_right() {
    run_and_retry(|| {
        test_aarch64_rule_with_lhs_termname(
            "iadd_extend_right",
            "iadd",
            vec![
                (Bitwidth::I8, VerificationResult::Success),
                (Bitwidth::I16, VerificationResult::Success),
                (Bitwidth::I32, VerificationResult::Success),
                (Bitwidth::I64, VerificationResult::InapplicableRule),
            ],
        )
    });
}

#[test]
fn test_named_iadd_extend_right_concrete() {
    test_concrete_aarch64_rule_with_lhs_termname(
        "iadd_extend_right",
        "iadd",
        false,
        ConcreteTest {
            termname: "iadd".to_string(),
            args: vec![
                ConcreteInput {
                    literal: "#b0000000000000001".to_string(),
                    ty: veri_ir::Type::BitVector(Some(16)),
                },
                ConcreteInput {
                    literal: "#b1111111111111111".to_string(),
                    ty: veri_ir::Type::BitVector(Some(16)),
                },
            ],
            output: ConcreteInput {
                literal: "#b0000000000000000".to_string(),
                ty: veri_ir::Type::BitVector(Some(16)),
            },
        },
    );
    test_concrete_aarch64_rule_with_lhs_termname(
        "iadd_extend_right",
        "iadd",
        false,
        ConcreteTest {
            termname: "iadd".to_string(),
            args: vec![
                ConcreteInput {
                    literal: "#b01000000000000000000000000000000".to_string(),
                    ty: veri_ir::Type::BitVector(Some(32)),
                },
                ConcreteInput {
                    literal: "#b00000000000000001111111111111111".to_string(),
                    ty: veri_ir::Type::BitVector(Some(32)),
                },
            ],
            output: ConcreteInput {
                literal: "#b01000000000000001111111111111111".to_string(),
                ty: veri_ir::Type::BitVector(Some(32)),
            },
        },
    )
}

#[test]
fn test_named_iadd_extend_left() {
    run_and_retry(|| {
        test_aarch64_rule_with_lhs_termname(
            "iadd_extend_left",
            "iadd",
            vec![
                (Bitwidth::I8, VerificationResult::Success),
                (Bitwidth::I16, VerificationResult::Success),
                (Bitwidth::I32, VerificationResult::Success),
                (Bitwidth::I64, VerificationResult::InapplicableRule),
            ],
        )
    });
}

#[test]
fn test_broken_iadd_extend() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/iadd/broken_add_extend.isle",
            "iadd".to_string(),
            vec![
                // The type of the iadd is the destination type, so for i8 there is no bad extend-to
                (Bitwidth::I8, VerificationResult::Success),
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
    });
}

#[test]
fn test_named_iadd_ishl_left() {
    run_and_retry(|| {
        test_aarch64_rule_with_lhs_termname("iadd_ishl_left", "iadd", lte_64_success_result())
    });
}

#[test]
fn test_named_iadd_ishl_right() {
    run_and_retry(|| {
        test_aarch64_rule_with_lhs_termname("iadd_ishl_right", "iadd", lte_64_success_result())
    });
}

#[test]
fn test_named_iadd_imul_right() {
    run_and_retry(|| {
        test_aarch64_rule_with_lhs_termname(
            "iadd_imul_right",
            "iadd",
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
fn test_named_iadd_imul_left() {
    run_and_retry(|| {
        test_aarch64_rule_with_lhs_termname(
            "iadd_imul_left",
            "iadd",
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
fn test_named_isub_imul() {
    run_and_retry(|| {
        test_aarch64_rule_with_lhs_termname(
            "isub_imul",
            "isub",
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
fn test_broken_iadd_imul_right() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/broken/iadd/broken_madd.isle",
            "iadd".to_string(),
            all_failure_result(),
        )
    });
}

#[test]
fn test_broken_iadd_imul_left() {
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
fn test_named_isub_base_case() {
    run_and_retry(|| {
        test_aarch64_rule_with_lhs_termname("isub_base_case", "isub", lte_64_success_result())
    })
}

#[test]
fn test_named_isub_imm12() {
    run_and_retry(|| {
        test_aarch64_rule_with_lhs_termname("isub_imm12", "isub", lte_64_success_result())
    })
}

#[test]
fn test_named_isub_imm12_concrete() {
    run_and_retry(|| {
        test_concrete_aarch64_rule_with_lhs_termname(
            "isub_imm12",
            "isub",
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
                output: ConcreteInput {
                    literal: "#b00000010".to_string(),
                    ty: veri_ir::Type::BitVector(Some(8)),
                },
            },
        )
    });
}

#[test]
fn test_named_isub_imm12_neg_not_distinct() {
    run_and_retry(|| {
        test_aarch64_rule_with_lhs_termname(
            "isub_imm12_neg",
            "isub",
            vec![
                (Bitwidth::I8, VerificationResult::NoDistinctModels),
                (Bitwidth::I16, VerificationResult::NoDistinctModels),
                (Bitwidth::I32, VerificationResult::NoDistinctModels),
                (Bitwidth::I64, VerificationResult::Success),
            ],
        );
    })
}

// Need a file test because this is a change on top of our latest rebase
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
fn test_named_isub_imm12_neg_concrete32() {
    run_and_retry(|| {
        test_concrete_aarch64_rule_with_lhs_termname(
            "isub_imm12_neg",
            "isub",
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
                output: ConcreteInput {
                    literal: "#b0000000000000000000000000000000000000000000000000000000000000010"
                        .to_string(),
                    ty: veri_ir::Type::BitVector(Some(64)),
                },
            },
        )
    });
}

#[test]
fn test_named_isub_imm12_neg_concrete64() {
    run_and_retry(|| {
        test_concrete_aarch64_rule_with_lhs_termname(
            "isub_imm12_neg",
            "isub",
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
                output: ConcreteInput {
                    literal: "#b0000000000000000000000000000000000000000000000000000000000000010"
                        .to_string(),
                    ty: veri_ir::Type::BitVector(Some(64)),
                },
            },
        )
    });
}

#[test]
fn test_named_isub_extend() {
    run_and_retry(|| {
        test_aarch64_rule_with_lhs_termname(
            "isub_extend",
            "isub",
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
fn test_named_isub_ishl() {
    run_and_retry(|| {
        test_aarch64_rule_with_lhs_termname("isub_ishl", "isub", lte_64_success_result())
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
fn test_named_ineg_base_case() {
    run_and_retry(|| {
        test_aarch64_rule_with_lhs_termname("ineg_base_case", "ineg", lte_64_success_result())
    })
}

#[test]
fn test_imul_base_case() {
    run_and_retry(|| {
        test_aarch64_rule_with_lhs_termname(
            "imul_base_case",
            "imul",
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

// TODO traps https://github.com/avanhatt/wasmtime/issues/31
#[test]
fn test_named_udiv() {
    run_and_retry(|| {
        test_aarch64_rule_with_lhs_termname(
            "udiv",
            "udiv",
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
fn test_named_sdiv_base_case() {
    run_and_retry(|| {
        test_aarch64_rule_with_lhs_termname(
            "sdiv_base_case",
            "sdiv",
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
fn test_named_sdiv_safe_divisor() {
    run_and_retry(|| {
        test_aarch64_rule_with_lhs_termname(
            "sdiv_safe_divisor",
            "sdiv",
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
fn test_named_srem() {
    run_and_retry(|| {
        test_aarch64_rule_with_lhs_termname(
            "srem",
            "srem",
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
fn test_named_urem() {
    run_and_retry(|| {
        test_aarch64_rule_with_lhs_termname(
            "urem",
            "urem",
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
fn test_named_urem_concrete() {
    run_and_retry(|| {
        test_concrete_aarch64_rule_with_lhs_termname(
            "urem",
            "urem",
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
                output: ConcreteInput {
                    literal: "#b00001001".to_string(),
                    ty: veri_ir::Type::BitVector(Some(8)),
                },
            },
        )
    });
}

#[test]
fn test_named_uextend() {
    run_and_retry(|| {
        test_aarch64_rule_with_lhs_termname("uextend", "uextend", all_success_result())
    })
}

#[test]
fn test_named_sextend() {
    run_and_retry(|| {
        test_aarch64_rule_with_lhs_termname("sextend", "sextend", all_success_result())
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
        let config = Config {
            dyn_width: false,
            term: "small_rotr".to_string(),
            distinct_check: true,
            custom_verification_condition: Some(Box::new(|smt, args, lhs, rhs| {
                let ty_arg = *args.first().unwrap();
                let lower_8_bits_eq = {
                    let mask = smt.atom("#x00000000000000FF");
                    smt.eq(smt.bvand(mask, lhs), smt.bvand(mask, rhs))
                };
                let lower_16_bits_eq = {
                    let mask = smt.atom("#x000000000000FFFF");
                    smt.eq(smt.bvand(mask, lhs), smt.bvand(mask, rhs))
                };
                smt.ite(
                    smt.eq(ty_arg, smt.atom("8")),
                    lower_8_bits_eq,
                    lower_16_bits_eq,
                )
            })),
            names: None,
        };
        test_from_file_with_config(
            "./examples/rotr/small_rotr_to_shifts.isle",
            config,
            vec![(Bitwidth::I64, VerificationResult::Success)],
        );
    })
}

#[test]
fn test_small_rotr_to_shifts_broken() {
    run_and_retry(|| {
        let config = Config {
            dyn_width: false,
            term: "small_rotr".to_string(),
            distinct_check: true,
            custom_verification_condition: Some(Box::new(|smt, args, lhs, rhs| {
                let ty_arg = *args.first().unwrap();
                let lower_8_bits_eq = {
                    let mask = smt.atom("#x00000000000000FF");
                    smt.eq(smt.bvand(mask, lhs), smt.bvand(mask, rhs))
                };
                let lower_16_bits_eq = {
                    let mask = smt.atom("#x000000000000FFFF");
                    smt.eq(smt.bvand(mask, lhs), smt.bvand(mask, rhs))
                };
                smt.ite(
                    smt.eq(ty_arg, smt.atom("8")),
                    lower_8_bits_eq,
                    lower_16_bits_eq,
                )
            })),
            names: None,
        };
        test_from_file_with_config(
            "./examples/broken/broken_mask_small_rotr.isle",
            config,
            vec![(
                Bitwidth::I64,
                VerificationResult::Failure(Counterexample {}),
            )],
        );
    })
}

#[test]
fn test_small_rotr_to_shifts_broken2() {
    run_and_retry(|| {
        let config = Config {
            dyn_width: false,
            term: "small_rotr".to_string(),
            distinct_check: true,
            custom_verification_condition: Some(Box::new(|smt, args, lhs, rhs| {
                let ty_arg = *args.first().unwrap();
                let lower_8_bits_eq = {
                    let mask = smt.atom("#x00000000000000FF");
                    smt.eq(smt.bvand(mask, lhs), smt.bvand(mask, rhs))
                };
                let lower_16_bits_eq = {
                    let mask = smt.atom("#x000000000000FFFF");
                    smt.eq(smt.bvand(mask, lhs), smt.bvand(mask, rhs))
                };
                smt.ite(
                    smt.eq(ty_arg, smt.atom("8")),
                    lower_8_bits_eq,
                    lower_16_bits_eq,
                )
            })),
            names: None,
        };
        test_from_file_with_config(
            "./examples/broken/broken_rule_or_small_rotr.isle",
            config,
            vec![(
                Bitwidth::I64,
                VerificationResult::Failure(Counterexample {}),
            )],
        );
    })
}

#[test]
fn test_small_rotr_imm_to_shifts() {
    run_and_retry(|| {
        let config = Config {
            dyn_width: false,
            term: "small_rotr_imm".to_string(),
            distinct_check: true,
            custom_verification_condition: Some(Box::new(|smt, args, lhs, rhs| {
                let ty_arg = *args.first().unwrap();
                let lower_8_bits_eq = {
                    let mask = smt.atom("#x00000000000000FF");
                    smt.eq(smt.bvand(mask, lhs), smt.bvand(mask, rhs))
                };
                let lower_16_bits_eq = {
                    let mask = smt.atom("#x000000000000FFFF");
                    smt.eq(smt.bvand(mask, lhs), smt.bvand(mask, rhs))
                };
                smt.ite(
                    smt.eq(ty_arg, smt.atom("8")),
                    lower_8_bits_eq,
                    lower_16_bits_eq,
                )
            })),
            names: None,
        };
        test_from_file_with_config(
            "./examples/rotr/small_rotr_imm_to_shifts.isle",
            config,
            vec![(Bitwidth::I64, VerificationResult::Success)],
        );
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
            "./examples/rotr/fits_in_16_with_imm_rotr.isle",
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
fn test_named_band_fits_in_32() {
    run_and_retry(|| {
        test_aarch64_rule_with_lhs_termname(
            "band_fits_in_32",
            "band",
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
fn test_broken_band_fits_in_32() {
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
fn test_named_band_64() {
    run_and_retry(|| {
        test_aarch64_rule_with_lhs_termname(
            "band_64",
            "band",
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
fn test_named_bor_fits_in_32() {
    run_and_retry(|| {
        test_aarch64_rule_with_lhs_termname(
            "bor_fits_in_32",
            "bor",
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
fn test_named_bor_64() {
    run_and_retry(|| {
        test_aarch64_rule_with_lhs_termname(
            "bor_64",
            "bor",
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
fn test_broken_bor_fits_in_32() {
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
fn test_named_bxor_fits_in_32() {
    run_and_retry(|| {
        test_aarch64_rule_with_lhs_termname(
            "bxor_fits_in_32",
            "bxor",
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
fn test_named_bxor_64() {
    run_and_retry(|| {
        test_aarch64_rule_with_lhs_termname(
            "bxor_64",
            "bxor",
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
fn test_named_band_not_fits_in_32() {
    run_and_retry(|| {
        test_aarch64_rule_with_lhs_termname(
            "band_not_fits_in_32",
            "band_not",
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
fn test_named_band_not_64() {
    run_and_retry(|| {
        test_aarch64_rule_with_lhs_termname(
            "band_not_64",
            "band_not",
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
fn test_named_bnot() {
    run_and_retry(|| {
        test_aarch64_rule_with_lhs_termname("bnot_base_case", "bnot", all_success_result())
    })
}

#[test]
fn test_named_bnot_ishl() {
    run_and_retry(|| test_aarch64_rule_with_lhs_termname("bnot_ishl", "bnot", all_success_result()))
}

#[test]
fn test_named_ishl_64() {
    test_aarch64_rule_with_lhs_termname(
        "ishl_64",
        "ishl",
        vec![
            (Bitwidth::I8, VerificationResult::InapplicableRule),
            (Bitwidth::I16, VerificationResult::InapplicableRule),
            (Bitwidth::I32, VerificationResult::InapplicableRule),
            (Bitwidth::I64, VerificationResult::Success),
        ],
    )
}

#[test]
fn test_named_ishl_64_concrete() {
    run_and_retry(|| {
        test_concrete_aarch64_rule_with_lhs_termname(
            "ishl_64",
            "ishl",
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
                output: ConcreteInput {
                    literal: "#b0000000000000000000000000000000000000000000000000000000000000100"
                        .to_string(),
                    ty: veri_ir::Type::BitVector(Some(64)),
                },
            },
        )
    });
}

#[test]
fn test_named_ishl_fits_in_32() {
    test_aarch64_rule_with_lhs_termname(
        "ishl_fits_in_32",
        "ishl",
        vec![
            (Bitwidth::I8, VerificationResult::Success),
            (Bitwidth::I16, VerificationResult::Success),
            (Bitwidth::I32, VerificationResult::Success),
            (Bitwidth::I64, VerificationResult::InapplicableRule),
        ],
    )
}

#[test]
fn test_named_ishl_fits_in_32_concrete() {
    run_and_retry(|| {
        test_concrete_aarch64_rule_with_lhs_termname(
            "ishl_fits_in_32",
            "ishl",
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
                output: ConcreteInput {
                    literal: "#b00000100".to_string(),
                    ty: veri_ir::Type::BitVector(Some(8)),
                },
            },
        )
    });
}

#[test]
fn test_named_sshr_64() {
    test_aarch64_rule_with_lhs_termname(
        "sshr_64",
        "sshr",
        vec![
            (Bitwidth::I8, VerificationResult::InapplicableRule),
            (Bitwidth::I16, VerificationResult::InapplicableRule),
            (Bitwidth::I32, VerificationResult::InapplicableRule),
            (Bitwidth::I64, VerificationResult::Success),
        ],
    )
}

#[test]
fn test_named_sshr_fits_in_32() {
    test_aarch64_rule_with_lhs_termname(
        "sshr_fits_in_32",
        "sshr",
        vec![
            (Bitwidth::I8, VerificationResult::Success),
            (Bitwidth::I16, VerificationResult::Success),
            (Bitwidth::I32, VerificationResult::Success),
            (Bitwidth::I64, VerificationResult::InapplicableRule),
        ],
    )
}

#[test]
fn test_named_sshr_fits_in_32_concrete() {
    test_concrete_aarch64_rule_with_lhs_termname(
        "sshr_fits_in_32",
        "sshr",
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
            output: ConcreteInput {
                literal: "#b11010000".to_string(),
                ty: veri_ir::Type::BitVector(Some(8)),
            },
        },
    )
}

#[test]
fn test_named_ushr_64() {
    test_aarch64_rule_with_lhs_termname(
        "ushr_64",
        "ushr",
        vec![
            (Bitwidth::I8, VerificationResult::InapplicableRule),
            (Bitwidth::I16, VerificationResult::InapplicableRule),
            (Bitwidth::I32, VerificationResult::InapplicableRule),
            (Bitwidth::I64, VerificationResult::Success),
        ],
    )
}

#[test]
fn test_named_ushr_fits_in_32() {
    test_aarch64_rule_with_lhs_termname(
        "ushr_fits_in_32",
        "ushr",
        vec![
            (Bitwidth::I8, VerificationResult::Success),
            (Bitwidth::I16, VerificationResult::Success),
            (Bitwidth::I32, VerificationResult::Success),
            (Bitwidth::I64, VerificationResult::InapplicableRule),
        ],
    )
}

#[test]
fn test_named_ushr_fits_in_32_concrete() {
    test_concrete_aarch64_rule_with_lhs_termname(
        "ushr_fits_in_32",
        "ushr",
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
            output: ConcreteInput {
                literal: "#b01010000".to_string(),
                ty: veri_ir::Type::BitVector(Some(8)),
            },
        },
    )
}

#[test]
fn test_named_do_shift_64_base_case() {
    run_and_retry(|| {
        test_aarch64_rule_with_lhs_termname(
            "do_shift_64_base_case",
            "do_shift",
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
fn test_named_do_shift_imm() {
    let config = Config {
        dyn_width: false,
        term: "do_shift".to_string(),
        distinct_check: true,
        custom_verification_condition: Some(Box::new(|smt, _args, lhs, rhs| {
            let lower_8_bits_eq = {
                let mask = smt.atom("#x00000000000000FF");
                smt.eq(smt.bvand(mask, lhs), smt.bvand(mask, rhs))
            };
            lower_8_bits_eq
        })),
        names: Some(vec!["do_shift_imm".to_string()]),
    };
    test_aarch64_with_config(config, vec![(Bitwidth::I8, VerificationResult::Success)]);
    let config = Config {
        dyn_width: false,
        term: "do_shift".to_string(),
        distinct_check: true,
        custom_verification_condition: Some(Box::new(|smt, _args, lhs, rhs| {
            let lower_16_bits_eq = {
                let mask = smt.atom("#x000000000000FFFF");
                smt.eq(smt.bvand(mask, lhs), smt.bvand(mask, rhs))
            };
            lower_16_bits_eq
        })),
        names: Some(vec!["do_shift_imm".to_string()]),
    };
    test_aarch64_with_config(config, vec![(Bitwidth::I16, VerificationResult::Success)]);
    let config = Config {
        dyn_width: false,
        term: "do_shift".to_string(),
        distinct_check: true,
        custom_verification_condition: Some(Box::new(|smt, _args, lhs, rhs| {
            let lower_32_bits_eq = {
                let mask = smt.atom("#x00000000FFFFFFFF");
                smt.eq(smt.bvand(mask, lhs), smt.bvand(mask, rhs))
            };
            lower_32_bits_eq
        })),
        names: Some(vec!["do_shift_imm".to_string()]),
    };
    test_aarch64_with_config(config, vec![(Bitwidth::I32, VerificationResult::Success)]);
    test_aarch64_rule_with_lhs_termname(
        "do_shift_imm",
        "do_shift",
        vec![(Bitwidth::I64, VerificationResult::Success)],
    )
}

#[test]
fn test_named_do_shift_fits_in_16() {
    run_and_retry(|| {
        let config = Config {
            dyn_width: false,
            term: "do_shift".to_string(),
            distinct_check: true,
            custom_verification_condition: Some(Box::new(|smt, args, lhs, rhs| {
                let ty_arg = args[1];
                let lower_8_bits_eq = {
                    let mask = smt.atom("#x00000000000000FF");
                    smt.eq(smt.bvand(mask, lhs), smt.bvand(mask, rhs))
                };
                let lower_16_bits_eq = {
                    let mask = smt.atom("#x000000000000FFFF");
                    smt.eq(smt.bvand(mask, lhs), smt.bvand(mask, rhs))
                };
                smt.ite(
                    smt.eq(ty_arg, smt.atom("8")),
                    lower_8_bits_eq,
                    lower_16_bits_eq,
                )
            })),
            names: Some(vec!["do_shift_fits_in_16".to_string()]),
        };
        test_aarch64_with_config(
            config,
            vec![
                (Bitwidth::I8, VerificationResult::Success),
                (Bitwidth::I16, VerificationResult::Success),
            ],
        );
    });
    test_aarch64_rule_with_lhs_termname(
        "do_shift_fits_in_16",
        "do_shift",
        vec![
            (Bitwidth::I32, VerificationResult::InapplicableRule),
            (Bitwidth::I64, VerificationResult::InapplicableRule),
        ],
    )
}

#[test]
fn test_named_do_shift_fits_in_16_concrete() {
    // (decl do_shift (ALUOp Type Reg Value) Reg)
    run_and_retry(|| {
        test_concrete_aarch64_rule_with_lhs_termname(
            "do_shift_fits_in_16",
            "do_shift",
            false,
            ConcreteTest {
                termname: "do_shift".to_string(),
                args: vec![
                    ConcreteInput {
                        literal: "#b00010010".to_string(),
                        ty: veri_ir::Type::BitVector(Some(8)),
                    },
                    ConcreteInput {
                        literal: "16".to_string(),
                        ty: veri_ir::Type::Int,
                    },
                    ConcreteInput {
                        literal:
                            "#b0000000000000000000000000000000000000000000000000000000000000001"
                                .to_string(),
                        ty: veri_ir::Type::BitVector(Some(64)),
                    },
                    ConcreteInput {
                        literal: "#b0000000000000001".to_string(),
                        ty: veri_ir::Type::BitVector(Some(16)),
                    },
                ],
                output: ConcreteInput {
                    literal: "#b0000000000000000000000000000000000000000000000000000000000000010"
                        .to_string(),
                    ty: veri_ir::Type::BitVector(Some(64)),
                },
            },
        )
    });
}

#[test]
fn test_named_do_shift_32_base_case() {
    test_aarch64_rule_with_lhs_termname(
        "do_shift_32_base_case",
        "do_shift",
        vec![
            (Bitwidth::I8, VerificationResult::InapplicableRule),
            (Bitwidth::I16, VerificationResult::InapplicableRule),
            (Bitwidth::I64, VerificationResult::InapplicableRule),
        ],
    );
    let config = Config {
        dyn_width: false,
        term: "do_shift".to_string(),
        distinct_check: true,
        custom_verification_condition: Some(Box::new(|smt, _args, lhs, rhs| {
            let lower_32_bits_eq = {
                let mask = smt.atom("#x00000000FFFFFFFF");
                smt.eq(smt.bvand(mask, lhs), smt.bvand(mask, rhs))
            };
            lower_32_bits_eq
        })),
        names: Some(vec!["do_shift_32_base_case".to_string()]),
    };
    test_aarch64_with_config(config, vec![(Bitwidth::I32, VerificationResult::Success)]);
}

#[test]
fn test_broken_do_shift_32() {
    test_from_file_with_lhs_termname(
        "./examples/broken/shifts/broken_do_shift_32.isle",
        "do_shift".to_string(),
        vec![
            (Bitwidth::I8, VerificationResult::InapplicableRule),
            (Bitwidth::I16, VerificationResult::InapplicableRule),
            (Bitwidth::I64, VerificationResult::InapplicableRule),
        ],
    );
    let config = Config {
        dyn_width: false,
        term: "do_shift".to_string(),
        distinct_check: true,
        custom_verification_condition: Some(Box::new(|smt, _args, lhs, rhs| {
            let lower_32_bits_eq = {
                let mask = smt.atom("#x00000000FFFFFFFF");
                smt.eq(smt.bvand(mask, lhs), smt.bvand(mask, rhs))
            };
            lower_32_bits_eq
        })),
        names: None,
    };
    test_aarch64_with_config(
        config,
        vec![(
            Bitwidth::I32,
            VerificationResult::Failure(Counterexample {}),
        )],
    );
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
            output: ConcreteInput {
                literal: "#b01010000".to_string(),
                ty: veri_ir::Type::BitVector(Some(8)),
            },
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
fn test_if_let() {
    test_from_file_with_lhs_termname(
        "./examples/constructs/if-let.isle",
        "iadd".to_string(),
        all_success_result(),
    );
}

#[test]
fn test_icmp_to_lower_icmp() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/icmp/icmp_to_lower_icmp.isle",
            "icmp".to_string(),
            vec![
                (Bitwidth::I8, VerificationResult::Success),
                (Bitwidth::I16, VerificationResult::Success),
                (Bitwidth::I32, VerificationResult::Success),
                (Bitwidth::I64, VerificationResult::Success),
            ],
        )
    })
}

#[test]
fn test_lower_icmp_into_reg() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/icmp/lower_icmp_into_reg.isle",
            "lower_icmp_into_reg".to_string(),
            vec![
                (Bitwidth::I8, VerificationResult::Success),
                (Bitwidth::I16, VerificationResult::Success),
                (Bitwidth::I32, VerificationResult::Success),
                (Bitwidth::I64, VerificationResult::Success),
            ],
        )
    })
}

#[test]
fn test_lower_icmp_into_reg_concrete_eq1() {
    run_and_retry(|| {
        test_concrete_input_from_file_with_lhs_termname(
            "./examples/icmp/lower_icmp_into_reg.isle",
            "lower_icmp_into_reg".to_string(),
            false,
            ConcreteTest {
                termname: "lower_icmp_into_reg".to_string(),
                args: vec![
                    ConcreteInput {
                        literal: "#b00000000".to_string(),
                        ty: veri_ir::Type::BitVector(Some(8)),
                    },
                    ConcreteInput {
                        literal: "#b00000000".to_string(),
                        ty: veri_ir::Type::BitVector(Some(8)),
                    },
                    ConcreteInput {
                        literal: "#b00000001".to_string(),
                        ty: veri_ir::Type::BitVector(Some(8)),
                    },
                    ConcreteInput {
                        literal: "8".to_string(),
                        ty: veri_ir::Type::Int,
                    },
                    ConcreteInput {
                        literal: "8".to_string(),
                        ty: veri_ir::Type::Int,
                    },
                ],
                output: ConcreteInput {
                    literal: "#b00000000".to_string(),
                    ty: veri_ir::Type::BitVector(Some(8)),
                },
            },
        )
    });
}

#[test]
fn test_lower_icmp_into_reg_concrete_eq2() {
    run_and_retry(|| {
        test_concrete_input_from_file_with_lhs_termname(
            "./examples/icmp/lower_icmp_into_reg.isle",
            "lower_icmp_into_reg".to_string(),
            false,
            ConcreteTest {
                termname: "lower_icmp_into_reg".to_string(),
                args: vec![
                    ConcreteInput {
                        literal: "#b00000000".to_string(),
                        ty: veri_ir::Type::BitVector(Some(8)),
                    },
                    ConcreteInput {
                        literal: "#b00000000".to_string(),
                        ty: veri_ir::Type::BitVector(Some(8)),
                    },
                    ConcreteInput {
                        literal: "#b00000000".to_string(),
                        ty: veri_ir::Type::BitVector(Some(8)),
                    },
                    ConcreteInput {
                        literal: "8".to_string(),
                        ty: veri_ir::Type::Int,
                    },
                    ConcreteInput {
                        literal: "8".to_string(),
                        ty: veri_ir::Type::Int,
                    },
                ],
                output: ConcreteInput {
                    literal: "#b00000001".to_string(),
                    ty: veri_ir::Type::BitVector(Some(8)),
                },
            },
        )
    });
}

#[test]
fn test_lower_icmp_32_64() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/icmp/lower_icmp_32_64.isle",
            "lower_icmp".to_string(),
            vec![
                // These fail to type check, rule is inapplicable because of priorities
                // (Bitwidth::I8, VerificationResult::Failure(Counterexample { })),
                // (Bitwidth::I16, VerificationResult::Failure(Counterexample { })),
                (Bitwidth::I32, VerificationResult::Success),
                (Bitwidth::I64, VerificationResult::Success),
            ],
        )
    })
}

#[test]
fn test_lower_icmp_fits_in_16_signed() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/icmp/lower_icmp_fits_in_16_signed.isle",
            "lower_icmp".to_string(),
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
fn test_lower_icmp_fits_in_16_unsigned_imm() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/icmp/lower_icmp_fits_in_16_unsigned_imm.isle",
            "lower_icmp".to_string(),
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
fn test_lower_icmp_fits_in_16_unsigned() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/icmp/lower_icmp_fits_in_16_unsigned.isle",
            "lower_icmp".to_string(),
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
fn test_lower_icmp_32_64_to_lower_icmp_const() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/icmp/lower_icmp_32_64_to_lower_icmp_const.isle",
            "lower_icmp".to_string(),
            vec![
                (Bitwidth::I8, VerificationResult::InapplicableRule),
                (Bitwidth::I16, VerificationResult::InapplicableRule),
                (Bitwidth::I32, VerificationResult::Success),
                (Bitwidth::I64, VerificationResult::Success),
            ],
        )
    })
}

#[test]
fn test_lower_icmp_const_32_64_imm() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/icmp/lower_icmp_const_32_64_imm.isle",
            "lower_icmp_const".to_string(),
            vec![
                (Bitwidth::I8, VerificationResult::InapplicableRule),
                (Bitwidth::I16, VerificationResult::InapplicableRule),
                (Bitwidth::I32, VerificationResult::Success),
                (Bitwidth::I64, VerificationResult::Success),
            ],
        )
    })
}

#[test]
fn test_lower_icmp_const_32_64_sgte() {
    // Note: only one distinct condition code is matched on, so need to disable
    // distinctness check
    run_and_retry(|| {
        let config = Config {
            dyn_width: false,
            term: "lower_icmp_const".to_string(),
            distinct_check: false,
            custom_verification_condition: None,
            names: None,
        };
        test_from_file_with_config(
            "./examples/icmp/lower_icmp_const_32_64_sgte.isle",
            config,
            vec![
                (Bitwidth::I8, VerificationResult::InapplicableRule),
                (Bitwidth::I16, VerificationResult::InapplicableRule),
                // Currently fails! The rewrite is not semantics-preserving
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
    })
}

#[test]
fn test_lower_icmp_const_32_64_ugte() {
    // Note: only one distinct condition code is matched on, so need to disable
    // distinctness check
    run_and_retry(|| {
        let config = Config {
            dyn_width: false,
            term: "lower_icmp_const".to_string(),
            distinct_check: false,
            custom_verification_condition: None,
            names: None,
        };
        test_from_file_with_config(
            "./examples/icmp/lower_icmp_const_32_64_ugte.isle",
            config,
            vec![
                (Bitwidth::I8, VerificationResult::InapplicableRule),
                (Bitwidth::I16, VerificationResult::InapplicableRule),
                // Currently fails! The rewrite is not semantics-preserving
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
    })
}

#[test]
fn test_lower_icmp_const_32_64() {
    run_and_retry(|| {
        test_from_file_with_lhs_termname(
            "./examples/icmp/lower_icmp_const_32_64.isle",
            "lower_icmp_const".to_string(),
            vec![
                (Bitwidth::I8, VerificationResult::InapplicableRule),
                (Bitwidth::I16, VerificationResult::InapplicableRule),
                (Bitwidth::I32, VerificationResult::Success),
                (Bitwidth::I64, VerificationResult::Success),
            ],
        )
    })
}
