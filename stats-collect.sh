#!/bin/sh

# Get a fixed revision of the spec tests.
if [ ! -d spec ] ; then
    git clone https://github.com/WebAssembly/spec.git
fi
cd spec ; git checkout 2a992ec2d30b0a7f0533ebdb5fe0cd7eb42553ca ; cd -

# Run all the tests.
for fn in spec/test/core/*.wast ; do
    ./target/debug/wasmtime wast $fn
done > rule-trace.csv
