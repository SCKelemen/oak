#!/bin/sh
# The element-wise span maps of map_add.oak through the native backend
# twice: as the search selects them (the vectorized forms,
# docs/spec/94-assembler.md §9 "Map vectorization") and with the
# `vectorize-maps` transform withheld (OAK_OPT_SKIP), the scalar loops the
# search then keeps. Each build prints the verdicts it shipped.
set -e
cd "$(dirname "$0")"
(cd ../.. && go run ./benchmarks/native/emit benchmarks/native/map_add.oak benchmarks/native/map_add_vector 2>&1 | grep "asm unit\|map vectorization" || true)
(cd ../.. && OAK_OPT_SKIP=vectorize-maps go run ./benchmarks/native/emit benchmarks/native/map_add.oak benchmarks/native/map_add_scalar 2>&1 | grep "asm unit" || true)
cc -std=c11 -O2 -w -DKERNEL_C='"map_add_vector.c"' -DLABEL='"vectorize-maps"' -o bench_map_vector bench_map.c map_add_vector.o
cc -std=c11 -O2 -w -DKERNEL_C='"map_add_scalar.c"' -DLABEL='"scalar loops"' -o bench_map_scalar bench_map.c map_add_scalar.o
echo "element-wise maps, 2^20 elements, best of 7 rounds of 200 calls, $(uname -m), load $(uptime | sed 's/.*averages*: //')"
./bench_map_vector
./bench_map_scalar
