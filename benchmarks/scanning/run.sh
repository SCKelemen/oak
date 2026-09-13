#!/bin/sh
# Builds every scanner against the shared input and prints one table.
# Vectorscan and RE2 come from Homebrew (brew install vectorscan re2); the
# Oak scanner is emitted from literals.oak by the compiler in this repo.
set -e
cd "$(dirname "$0")"
cc -std=c11 -O2 -o gen_input gen_input.c && ./gen_input
cc -std=c11 -O2 -o scan_c scan_c.c
cc -std=c11 -O2 -I/opt/homebrew/opt/vectorscan/include -L/opt/homebrew/opt/vectorscan/lib -lhs -o scan_hs scan_hs.c
clang++ -std=c++17 -O2 $(pkg-config --cflags re2) -o scan_re2 scan_re2.cc $(pkg-config --libs re2)
(cd ../.. && go run . build -emit-c benchmarks/scanning/literals.oak >/dev/null && mv literals.c benchmarks/scanning/literals.c)
cc -std=c11 -O2 -Wno-unused-function -Wno-unused-const-variable -o scan_oak scan_oak.c
echo "Multi-literal scanning, 16 literals, 64 MB text, best of 5, $(uname -m)"
./scan_oak
./scan_c
./scan_hs
./scan_re2
