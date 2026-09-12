// Writes 64 MB of random valid UTF-8 (60% ASCII, 20% two-byte, 10% three-byte,
// 10% four-byte code points) to input.bin, from the same generator every
// harness in this directory shares. Build: cc -O2 -o gen_input gen_input.c
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
typedef uint8_t u8; typedef uint32_t u32; typedef uint64_t u64;
static u64 rng_state = 0x9E3779B97F4A7C15ull;
static inline u32 rng(void) { u64 x = rng_state; x ^= x >> 12; x ^= x << 25; x ^= x >> 27; rng_state = x; return (u32)((x * 0x2545F4914F6CDD1Dull) >> 32); }
int main(void) {
    const u32 n = 64u << 20;
    u8 *buf = malloc(n + 4); u32 i = 0;
    while (i + 4 <= n) {
        u32 r = rng(); u32 kind = r % 10; u32 cp;
        if (kind < 6) cp = 32 + (r >> 8) % 95;
        else if (kind < 8) cp = 0x80 + (r >> 8) % (0x800 - 0x80);
        else if (kind < 9) { cp = 0x800 + (r >> 8) % (0xFFFF - 0x800); if (cp >= 0xD800 && cp <= 0xDFFF) cp = 0x4E00; }
        else cp = 0x10000 + (r >> 8) % (0x10FFFF - 0x10000);
        if (cp < 0x80) buf[i++] = (u8)cp;
        else if (cp < 0x800) { buf[i++] = (u8)(0xC0 | (cp >> 6)); buf[i++] = (u8)(0x80 | (cp & 63)); }
        else if (cp < 0x10000) { buf[i++] = (u8)(0xE0 | (cp >> 12)); buf[i++] = (u8)(0x80 | ((cp >> 6) & 63)); buf[i++] = (u8)(0x80 | (cp & 63)); }
        else { buf[i++] = (u8)(0xF0 | (cp >> 18)); buf[i++] = (u8)(0x80 | ((cp >> 12) & 63)); buf[i++] = (u8)(0x80 | ((cp >> 6) & 63)); buf[i++] = (u8)(0x80 | (cp & 63)); }
    }
    while (i < n) buf[i++] = 'a';
    FILE *f = fopen("input.bin", "wb"); fwrite(buf, 1, n, f); fclose(f);
    printf("wrote %u bytes\n", n);
    return 0;
}
