#include <stdint.h>

#ifdef FOUR_WAY_REFERENCE
/* Independent C reference, compiled separately without LTO or Oak C code. */
typedef struct oak_view_u32 { const uint32_t *base; uint32_t len; } View32;
typedef struct oak_view_u64 { const uint64_t *base; uint32_t len; } View64;
uint32_t c_sum32(View32 v) {
    uint32_t acc = 0;
    for (uint32_t i = 0; i < v.len; i++) acc += v.base[i];
    return acc;
}
uint64_t c_sum64(View64 v) {
    uint64_t acc = 0;
    for (uint32_t i = 0; i < v.len; i++) acc += v.base[i];
    return acc;
}
#else
#define main oak_program_main
#include "kernels.c"
#undef main
#include <errno.h>
#include <inttypes.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

_Static_assert(sizeof(oak_view_u32) == 16 && offsetof(oak_view_u32, len) == 8,
               "expected ARM64 pointer/u32 view ABI");
_Static_assert(sizeof(oak_view_u64) == 16 && offsetof(oak_view_u64, len) == 8,
               "expected ARM64 pointer/u32 view ABI");
#define DECLARE(lang) \
    extern uint32_t lang##_sum32(oak_view_u32); \
    extern uint64_t lang##_sum64(oak_view_u64)
DECLARE(c);
DECLARE(rust);
DECLARE(zig);

static unsigned number(const char *text, unsigned limit) {
    if (*text < '0' || *text > '9') exit(2);
    char *end;
    errno = 0;
    unsigned long value = strtoul(text, &end, 10);
    if (errno || *end || value > limit) exit(2);
    return (unsigned)value;
}
static uint64_t now_ns(void) {
    struct timespec ts;
    if (clock_gettime(CLOCK_MONOTONIC, &ts)) exit(2);
    return (uint64_t)ts.tv_sec * UINT64_C(1000000000) + (uint64_t)ts.tv_nsec;
}
static volatile uint64_t sink;

int main(int argc, char **argv) {
    if (argc != 6) return 2;
    int timed = !strcmp(argv[1], "measure");
    if (!timed && strcmp(argv[1], "check")) return 2;
    const char *names[] = {"oak-native", "c", "rust", "zig"};
    unsigned impl = 0;
    while (impl < 4 && strcmp(argv[2], names[impl])) impl++;
    if (impl == 4) return 2;
    unsigned width = number(argv[3], 64);
    unsigned n = number(argv[4], 1u << 20);
    unsigned calls = number(argv[5], 1u << 20);
    if ((width != 32 && width != 64) || calls == 0 || (!timed && calls != 1)) return 2;
    void *input = malloc((size_t)(n ? n : 1) * (width / 8));
    if (!input) return 2;
    uint64_t random = 42, expected = 0, bad = 0, begin = 0, elapsed = 0;
    if (width == 32) {
        uint32_t total = 0;
        for (unsigned i = 0; i < n; i++) {
            random = random * UINT64_C(6364136223846793005) + 1;
            ((u32 *)input)[i] = (u32)(random >> 32);
            total += ((u32 *)input)[i];
        }
        expected = total;
        u32 (*functions[])(oak_view_u32) = {oak_sum32, c_sum32, rust_sum32, zig_sum32};
        u32 (*volatile run)(oak_view_u32) = functions[impl];
        oak_view_u32 v = {.base = input, .len = n};
        for (unsigned i = 0; i < 3; i++) bad |= run(v) ^ total;
        if (timed) begin = now_ns();
        for (unsigned i = 0; i < calls; i++) {
            u32 result = run(v);
            bad |= result ^ total;
            sink = result;
        }
        if (timed) elapsed = now_ns() - begin;
    } else {
        for (unsigned i = 0; i < n; i++) {
            random = random * UINT64_C(6364136223846793005) + 1;
            ((u64 *)input)[i] = random;
            expected += random;
        }
        u64 (*functions[])(oak_view_u64) = {oak_sum64, c_sum64, rust_sum64, zig_sum64};
        u64 (*volatile run)(oak_view_u64) = functions[impl];
        oak_view_u64 v = {.base = input, .len = n};
        for (unsigned i = 0; i < 3; i++) bad |= run(v) ^ expected;
        if (timed) begin = now_ns();
        for (unsigned i = 0; i < calls; i++) {
            u64 result = run(v);
            bad |= result ^ expected;
            sink = result;
        }
        if (timed) elapsed = now_ns() - begin;
    }
    free(input);
    if (bad || (timed && !elapsed)) return 3;
    printf("{\"mode\":\"%s\",\"implementation\":\"%s\",\"width\":%u,"
           "\"elements\":%u,\"calls\":%u,\"checksum\":\"%016" PRIx64 "\"",
           argv[1], names[impl], width, n, calls, expected);
    if (timed) printf(",\"elapsed_ns\":%" PRIu64, elapsed);
    puts("}");
    return 0;
}
#endif
