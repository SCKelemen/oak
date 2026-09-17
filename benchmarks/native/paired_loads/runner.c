#define main oak_program_main
#include "kernels.c"
#undef main
#include <errno.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

static unsigned positive(const char *text, unsigned limit) {
    char *end;
    if (*text < '1' || *text > '9') exit(2);
    errno = 0;
    unsigned long value = strtoul(text, &end, 10);
    if (errno || *end || value == 0 || value > limit) exit(2);
    return (unsigned)value;
}
static uint64_t now_ns(void) {
    struct timespec ts;
    if (clock_gettime(CLOCK_MONOTONIC, &ts)) exit(2);
    return (uint64_t)ts.tv_sec * UINT64_C(1000000000) + (uint64_t)ts.tv_nsec;
}
static volatile uint64_t sink;

int main(int argc, char **argv) {
    if (argc != 4) return 2;
    unsigned width = positive(argv[1], 64);
    unsigned n = positive(argv[2], 1u << 20);
    unsigned calls = positive(argv[3], 1u << 20);
    if (width != 32 && width != 64) return 2;
    void *input = malloc((size_t)n * (width / 8));
    if (!input) return 2;
    uint64_t random = 42, expected = 0, bad = 0, begin, elapsed;
    if (width == 32) {
        uint32_t total = 0;
        for (unsigned i = 0; i < n; i++) {
            random = random * UINT64_C(6364136223846793005) + 1;
            ((u32 *)input)[i] = (u32)(random >> 32);
            total += ((u32 *)input)[i];
        }
        expected = total;
        oak_view_u32 v = {.base = input, .len = n};
        u32 (*volatile run)(oak_view_u32) = oak_sum32;
        for (unsigned i = 0; i < 3; i++) bad |= run(v) ^ total;
        begin = now_ns();
        for (unsigned i = 0; i < calls; i++) {
            u32 result = run(v);
            bad |= result ^ total;
            sink = result;
        }
        elapsed = now_ns() - begin;
    } else {
        for (unsigned i = 0; i < n; i++) {
            random = random * UINT64_C(6364136223846793005) + 1;
            ((u64 *)input)[i] = random;
            expected += random;
        }
        oak_view_u64 v = {.base = input, .len = n};
        u64 (*volatile run)(oak_view_u64) = oak_sum64;
        for (unsigned i = 0; i < 3; i++) bad |= run(v) ^ expected;
        begin = now_ns();
        for (unsigned i = 0; i < calls; i++) {
            u64 result = run(v);
            bad |= result ^ expected;
            sink = result;
        }
        elapsed = now_ns() - begin;
    }
    free(input);
    if (bad || !elapsed) return 3;
    printf("{\"elapsed_ns\":%" PRIu64 ",\"checksum\":\"%016" PRIx64 "\"}\n", elapsed, expected);
    return 0;
}
