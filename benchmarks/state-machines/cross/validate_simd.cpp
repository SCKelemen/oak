// SIMD validators: simdutf::validate_utf8 and simdjson::validate_utf8.
// Build: clang++ -std=c++17 -O2 -I/opt/homebrew/include -L/opt/homebrew/lib -lsimdutf -lsimdjson -o validate_simd validate_simd.cpp
#include <simdutf.h>
#include <simdjson.h>
extern "C" {
#include "timing.h"
}
int main() {
    uint64_t n; uint8_t *buf = read_input(&n);
    double best_u = 1e30, best_j = 1e30; bool ok_u = false, ok_j = false;
    for (int r = 0; r < 5; r++) {
        double t0 = now_ns(); ok_u = simdutf::validate_utf8((const char *)buf, n); double t = now_ns() - t0; if (t < best_u) best_u = t;
        t0 = now_ns(); ok_j = simdjson::validate_utf8((const char *)buf, n); t = now_ns() - t0; if (t < best_j) best_j = t;
    }
    REPORT("simdutf::validate_utf8 (SIMD)", best_u, n);
    REPORT("simdjson::validate_utf8 (SIMD)", best_j, n);
    return (ok_u && ok_j) ? 0 : 1;
}
