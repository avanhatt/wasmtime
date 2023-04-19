#!/bin/bash

commit=7e86d68e99e60130899fbe3b3ab6e9dce9187a7c
if [ ! -d webassembly-benchmarks ]; then
    git clone https://github.com/jedisct1/webassembly-benchmarks.git
fi
cd webassembly-benchmarks ; git checkout $commit ; cd -

ts=`date +'%Y-%m-%d-%s'`

for fn in webassembly-benchmarks/2022-12/wasm/*.wasm ; do
    echo $fn >&2
    ./target/debug/wasmtime compile --disable-cache \
        --disable-parallel-compilation $fn
done | grep '^\d*,' > rule-trace-$ts.csv
