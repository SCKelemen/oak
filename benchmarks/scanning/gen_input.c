// Writes 64 MB of deterministic random printable ASCII (a newline about
// every eighty bytes) with the literal set planted about once per 4 KiB, to
// input.bin. Every harness here shares it. Build: cc -O2 -o gen_input gen_input.c
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "literals.h"
typedef uint8_t u8; typedef uint32_t u32; typedef uint64_t u64;
static u64 rng_state = 0x9E3779B97F4A7C15ull;
static inline u32 rng(void) { u64 x = rng_state; x ^= x >> 12; x ^= x << 25; x ^= x >> 27; rng_state = x; return (u32)((x * 0x2545F4914F6CDD1Dull) >> 32); }
int main(void) {
    const u32 n = 64u << 20;
    u8 *buf = malloc(n);
    if (!buf) { fprintf(stderr, "out of memory\n"); return 2; }
    u32 i = 0, planted = 0;
    while (i < n) {
        u32 r = rng();
        if (r % 4096 == 0) {
            const char *lit = LITERALS[(r >> 12) % NLITERALS];
            size_t len = strlen(lit);
            if (i + len > n) break;
            memcpy(buf + i, lit, len); i += (u32)len; planted++;
            continue;
        }
        buf[i++] = (r % 80 == 0) ? '\n' : (u8)(32 + (r >> 8) % 95);
    }
    while (i < n) buf[i++] = 'a';
    FILE *f = fopen("input.bin", "wb");
    if (!f || fwrite(buf, 1, n, f) != n || fclose(f) != 0) { fprintf(stderr, "cannot write input.bin\n"); return 2; }
    printf("wrote %u bytes, %u literals planted\n", n, planted);
    return 0;
}
