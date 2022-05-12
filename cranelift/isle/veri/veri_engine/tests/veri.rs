mod utils;
use utils::{just_8_result, lte_64_success_result};
use utils::{test_from_file, test_from_file_custom_prelude, test_from_file_self_contained};

#[test]
fn test_iadds() {
    test_from_file_custom_prelude(
        "./tests/code/selfcontained/simple_prelude.isle",
        "./tests/code/selfcontained/simple_iadd.isle",
        lte_64_success_result(),
    );

    test_from_file_custom_prelude(
        "./tests/code/selfcontained/simple_prelude.isle",
        "./tests/code/selfcontained/iadd_to_sub.isle",
        lte_64_success_result(),
    );
}

#[test]
fn test_implicit_conversions() {
    test_from_file_custom_prelude(
        "./tests/code/selfcontained/prelude.isle",
        "./tests/code/selfcontained/simple_iadd_implicit_conv.isle",
        lte_64_success_result(),
    );

    test_from_file_custom_prelude(
        "./tests/code/selfcontained/prelude.isle",
        "./tests/code/selfcontained/iadd_to_sub_implicit_conv.isle",
        lte_64_success_result(),
    );
}

#[test]
fn test_iadd_from_file() {
    test_from_file("./examples/iadd.isle", lte_64_success_result())
}

#[test]
fn test_chained_iadd_from_file() {
    test_from_file(
        "./examples/iadd-two-rule-chain.isle",
        lte_64_success_result(),
    )
}

#[test]
fn test_ineg() {
    test_from_file(
        "./examples/ineg.isle",
        lte_64_success_result(),
    )
}

#[test]
fn test_let() {
    test_from_file_self_contained("./tests/code/selfcontained/let.isle", just_8_result());
}
