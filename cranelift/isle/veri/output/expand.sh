#!/usr/bin/env bash

set -exuo pipefail

function expand() {
    cargo run --bin expand -- \
        --codegen-crate-dir ../../codegen/ \
        --work-dir /tmp \
        --name aarch64 \
        "$@"
}

expand \
    --term-name sink_load_into_addr \
    > output/sink_load_into_addr.out

expand \
    --term-name sink_load_into_addr \
    --inline add_imm_to_addr \
    > output/sink_load_into_addr_inline_add_imm_to_addr.out

expand \
    --term-name sink_load_into_addr \
    --inline add_imm_to_addr \
    --inline add_imm \
    > output/sink_load_into_addr_inline_add_imm_to_addr_add_imm.out

expand \
    --term-name lower \
    > output/lower.out
