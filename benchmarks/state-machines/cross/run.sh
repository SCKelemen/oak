#!/bin/sh
# Builds every validator against the shared input and prints one table.
set -e
cd "$(dirname "$0")"
cc -std=c11 -O2 -o gen_input gen_input.c && ./gen_input
cc -std=c11 -O2 -Wno-unused-function -o oak_validate oak_validate.c -lm
go build -o validate_go validate.go
rustc -O -o validate_rs validate.rs 2>/dev/null
zig build-exe validate.zig -O ReleaseFast -lc -femit-bin=validate_zig
clang++ -std=c++17 -O2 -I/opt/homebrew/include -L/opt/homebrew/lib -lsimdutf -lsimdjson -o validate_simd validate_simd.cpp
cc -std=c11 -O2 -Wno-unused-function -Wno-unused-const-variable -o lowerings ../lowerings.c
echo "UTF-8 validation, 64 MB random valid text (60% ASCII), best of 5, $(uname -m)"
./oak_validate
./validate_go
./validate_rs
./validate_zig
./validate_simd
