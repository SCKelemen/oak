#!/bin/sh
# The same Oak validator through the C backend and through the native
# backend (docs/spec/93-simd.md section 1.4 "The native backend",
# docs/spec/94-assembler.md section 9), timed on the state-machines
# harness's 64 MB UTF-8 input. utf8_valid.oak is stdlib/utf8.oak's kernel
# with its tables passed in as one view (the native backend does not
# address globals yet).
set -e
cd "$(dirname "$0")"
in=../state-machines/cross/input.bin
[ -f "$in" ] || (cd ../state-machines/cross && cc -std=c11 -O2 -o gen_input gen_input.c && ./gen_input)
(cd ../.. && go run . build -emit-c -o benchmarks/native/utf8_valid_c.c benchmarks/native/utf8_valid.oak >/dev/null)
(cd ../.. && go run ./benchmarks/native/emit benchmarks/native/utf8_valid.oak benchmarks/native/utf8_valid_native 2>&1 | grep -v "asm unit\|^$" || true)
cc -std=c11 -O2 -w -DKERNEL_C='"utf8_valid_c.c"' -DLABEL='"C backend (clang -O2)"' -o bench_c bench_utf8.c
cc -std=c11 -O2 -w -DKERNEL_C='"utf8_valid_native.c"' -DLABEL='"native backend"' -o bench_native bench_utf8.c utf8_valid_native.o
echo "UTF-8 validator (tables as a view), 64 MB, best of 5, $(uname -m)"
./bench_c "$in"
./bench_native "$in"
