#!/bin/sh

for fn in tests/spec_testsuite/*.wast ; do
    ./target/debug/wasmtime wast $fn
done
# | grep '^\d*,' > rule-trace.csv
