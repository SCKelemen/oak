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
    unsigned long n = strtoul(text, &end, 10);
    if (errno || *end || n == 0 || n > limit) exit(2);
    return (unsigned)n;
}

static uint64_t now_ns(void) {
    struct timespec ts;
    if (clock_gettime(CLOCK_MONOTONIC, &ts)) exit(2);
    return (uint64_t)ts.tv_sec * UINT64_C(1000000000) + (uint64_t)ts.tv_nsec;
}

// Independent linear scan, outside timing; no sorted-search algorithm shared
// with the Oak implementation. Check every timed result against this oracle.
static uint32_t reference(uint32_t scalar) {
    size_t words = sizeof(grapheme_table.v) / sizeof(grapheme_table.v[0]);
    for (size_t i = 0; i + 2 < words; i += 3) {
        if (grapheme_table.v[i] <= scalar && scalar <= grapheme_table.v[i + 1])
            return grapheme_table.v[i + 2];
    }
    return 0;
}

static volatile uint64_t sink;
int main(int argc, char **argv) {
    if (argc != 3) return 2;
    unsigned mode = positive(argv[1], 3), rounds = positive(argv[2], 4096);
    enum { N = 4096 };
    uint32_t inputs[N], expected[N];
    uint64_t random = 42, checksum = 0;
    size_t entries = sizeof(grapheme_table.v) / sizeof(grapheme_table.v[0]) / 3;
    for (unsigned i = 0; i < N; i++) {
        random = random * UINT64_C(6364136223846793005) + 1;
        uint32_t r = (uint32_t)(random >> 32);
        if (mode == 1) inputs[i] = r % 128;
        else if (mode == 2) inputs[i] = r % 0x110000;
        else {
            size_t entry = (r % entries) * 3;
            inputs[i] = grapheme_table.v[entry + (i % 2)] + (i % 3) - 1;
        }
    }
    inputs[0] = 0; inputs[1] = UINT32_MAX; inputs[2] = 0x110000;
    for (unsigned i = 0; i < N; i++) expected[i] = reference(inputs[i]);
    uint32_t (*volatile run)(uint32_t) = oak_grapheme_class;
    uint32_t bad = 0;
    for (unsigned i = 0; i < N; i++) bad |= run(inputs[i]) ^ expected[i];
    uint64_t begin = now_ns();
    for (unsigned round = 0; round < rounds; round++) {
        for (unsigned i = 0; i < N; i++) {
            uint32_t result = run(inputs[i]);
            bad |= result ^ expected[i];
            checksum += result;
        }
    }
    uint64_t elapsed = now_ns() - begin;
    sink = checksum;
    if (bad || !elapsed) return 3;
    printf("{\"elapsed_ns\":%" PRIu64 ",\"checksum\":\"%016" PRIx64 "\"}\n", elapsed, checksum);
    return 0;
}
