#!/bin/bash

shopt -s extglob
tests=tests/spec_testsuite/!(simd*).wast

ts=`date +'%Y-%m-%d-%s'`

for fn in $tests ; do
    ./target/debug/wasmtime wast --disable-cache $fn
done | grep '^\d*,' > rule-trace-$ts.csv
