#!/bin/bash

set -exuo pipefail

tests_directory="$1"
working_directory=$(mktemp -d)

# Build.
cargo build --bin wasmtime --features 'wasmtime-cranelift/trace-log'

# Run.
trace_directory="${working_directory}/trace"
mkdir -p "${trace_directory}"

for test in "${tests_directory}"/*.wast ; do
    test_name=$(basename "${test}")
    log_prefix="${trace_directory}/${test_name}."
    RUST_LOG='isle_rule_trace=trace' \
        ./target/debug/wasmtime wast \
        -C compiler=cranelift \
        -C cache=no \
        -D log-to-files=y \
        -D log-prefix="${log_prefix}" \
        "${test}"
done
