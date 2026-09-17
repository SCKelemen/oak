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
static uint64_t checksum(const void *values, size_t size) {
    const unsigned char *bytes = values;
    uint64_t result = UINT64_C(14695981039346656037);
    for (size_t i = 0; i < size; i++) result = (result ^ bytes[i]) * UINT64_C(1099511628211);
    return result;
}
static volatile uint64_t sink;

int main(int argc, char **argv) {
    if (argc != 5) return 2;
    unsigned width = positive(argv[1], 64), form = positive(argv[2], 2);
    unsigned n = positive(argv[3], 1u << 24), calls = positive(argv[4], 1u << 20);
    if (width != 32 && width != 64) return 2;
    size_t size = (size_t)n * (width / 8);
    void *input = malloc(size), *output = malloc(size);
    if (!input || !output) { free(input); free(output); return 2; }
    uint64_t begin, elapsed, strict, fused;
    uint32_t random = 42;
    if (width == 32) {
        for (unsigned i = 0; i < n; i++) {
            random = random * UINT32_C(1664525) + UINT32_C(1013904223);
            ((f32 *)input)[i] = (f32)(random >> 24) * 0.25f;
        }
        oak_view_f32 a = {.base = input, .len = n};
        oak_span_f32 dst = {.base = output, .len = n};
        void (*volatile run)(oak_span_f32, oak_view_f32, f32, f32) = form == 1 ? oak_map32_strict : oak_map32_fused;
        oak_map32_strict(dst, a, 1.25f, 0.5f); strict = checksum(output, size);
        oak_map32_fused(dst, a, 1.25f, 0.5f); fused = checksum(output, size);
        if (strict != fused) { free(input); free(output); return 3; }
        for (unsigned i = 0; i < 3; i++) run(dst, a, 1.25f, 0.5f);
        begin = now_ns();
        for (unsigned i = 0; i < calls; i++) { run(dst, a, 1.25f, 0.5f); sink = (uint64_t)((f32 *)output)[0]; }
        elapsed = now_ns() - begin;
    } else {
        for (unsigned i = 0; i < n; i++) {
            random = random * UINT32_C(1664525) + UINT32_C(1013904223);
            ((f64 *)input)[i] = (f64)(random >> 24) * 0.25;
        }
        oak_view_f64 a = {.base = input, .len = n};
        oak_span_f64 dst = {.base = output, .len = n};
        void (*volatile run)(oak_span_f64, oak_view_f64, f64, f64) = form == 1 ? oak_map64_strict : oak_map64_fused;
        oak_map64_strict(dst, a, 1.25, 0.5); strict = checksum(output, size);
        oak_map64_fused(dst, a, 1.25, 0.5); fused = checksum(output, size);
        if (strict != fused) { free(input); free(output); return 3; }
        for (unsigned i = 0; i < 3; i++) run(dst, a, 1.25, 0.5);
        begin = now_ns();
        for (unsigned i = 0; i < calls; i++) { run(dst, a, 1.25, 0.5); sink = (uint64_t)((f64 *)output)[0]; }
        elapsed = now_ns() - begin;
    }
    if (checksum(output, size) != strict) { free(input); free(output); return 3; }
    printf("{\"elapsed_ns\":%" PRIu64 ",\"bits\":\"%016" PRIx64 "\"}\n", elapsed, strict);
    free(input); free(output);
    return 0;
}
