#define main oak_program_main
#include "kernels.c"
#undef main
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static uint64_t now_ns(void) {
    struct timespec ts;
    if (clock_gettime(CLOCK_MONOTONIC, &ts)) exit(2);
    return (uint64_t)ts.tv_sec * UINT64_C(1000000000) + (uint64_t)ts.tv_nsec;
}

static unsigned positive(const char *text, unsigned limit) {
    char *end;
    if (*text < '1' || *text > '9') exit(2);
    unsigned long value = strtoul(text, &end, 10);
    if (*end || value == 0 || value > limit) exit(2);
    return (unsigned)value;
}

static volatile uint64_t sink;

int main(int argc, char **argv) {
    if (argc != 5) return 2;
    unsigned width = positive(argv[1], 64), form = positive(argv[2], 2);
    unsigned n = positive(argv[3], 1u << 24), calls = positive(argv[4], 1u << 20);
    if (width != 32 && width != 64) return 2;
    u8 *left = malloc(n), *right = malloc(n);
    if (!left || !right) { free(left); free(right); return 2; }
    uint32_t random = 42;
    for (unsigned i = 0; i < n; i++) {
        random = random * UINT32_C(1664525) + UINT32_C(1013904223);
        left[i] = (u8)(random >> 24);
        random = random * UINT32_C(1664525) + UINT32_C(1013904223);
        right[i] = (u8)(random >> 24);
    }
    oak_view_u8 a = {.base = left, .len = n}, b = {.base = right, .len = n};
    uint64_t bits = 0, begin, elapsed;
    if (width == 32) {
        // Volatile indirect calls prevent the C baseline hoisting identical
        // pure calls out of the timed loop. No fast-math or contraction flags.
        f32 (*volatile run)(oak_view_u8, oak_view_u8) = form == 1 ? oak_dot32_strict : oak_dot32_fused;
        f32 strict = oak_dot32_strict(a, b), fused = oak_dot32_fused(a, b);
        uint32_t sb, fb;
        memcpy(&sb, &strict, sizeof sb); memcpy(&fb, &fused, sizeof fb);
        if (sb != fb) { free(left); free(right); return 3; }
        for (unsigned i = 0; i < 3; i++) sink = (uint64_t)run(a, b);
        begin = now_ns();
        for (unsigned i = 0; i < calls; i++) {
            f32 result = run(a, b);
            uint32_t value;
            memcpy(&value, &result, sizeof value);
            sink = value;
        }
        elapsed = now_ns() - begin;
        bits = sb;
    } else {
        f64 (*volatile run)(oak_view_u8, oak_view_u8) = form == 1 ? oak_dot64_strict : oak_dot64_fused;
        f64 strict = oak_dot64_strict(a, b), fused = oak_dot64_fused(a, b);
        uint64_t sb, fb;
        memcpy(&sb, &strict, sizeof sb); memcpy(&fb, &fused, sizeof fb);
        if (sb != fb) { free(left); free(right); return 3; }
        for (unsigned i = 0; i < 3; i++) sink = (uint64_t)run(a, b);
        begin = now_ns();
        for (unsigned i = 0; i < calls; i++) {
            f64 result = run(a, b);
            uint64_t value;
            memcpy(&value, &result, sizeof value);
            sink = value;
        }
        elapsed = now_ns() - begin;
        bits = sb;
    }
    printf("{\"elapsed_ns\":%" PRIu64 ",\"bits\":\"%016" PRIx64 "\"}\n", elapsed, bits);
    free(left); free(right);
    return 0;
}
