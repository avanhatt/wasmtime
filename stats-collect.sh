#!/bin/bash

# Exclude:
# simd*: All SIMD is out of scope.
# table-sub, table_copy, table_init, bulk, memory_fill, memory_copy:
#   bulk memory ops extension
# binary-leb128: Uses `trunc_sat_*` instructions, and seems to be mostly about
#   parsing the binary format anyway.
shopt -s extglob
tests=tests/spec_testsuite/!(simd*|table-sub|table_copy|table_init|bulk|memory_fill|memory_copy|binary-leb128).wast

# Remove `i(32|64).extend(8|16|32)_s` instructions and the tests that use
# them, which are part of the sign-extending operators extension.
sed -i.bak '/extend[0-9][0-9]*_s/d' tests/spec_testsuite/i32.wast
sed -i.bak '/extend[0-9][0-9]*_s/d' tests/spec_testsuite/i64.wast

# Same with `trunc_sat_f(32|64)_(s|u)` instructions, which are part of the
# non-trapping float-to-int extension.
sed -i.bak '/trunc_sat_/d' tests/spec_testsuite/conversions.wast

ts=`date +'%Y-%m-%d-%s'`

for fn in $tests ; do
    ./target/debug/wasmtime wast --disable-cache \
        --disable-parallel-compilation $fn
done | grep '^\d*,' > rule-trace-$ts.csv
