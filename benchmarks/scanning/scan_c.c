// Hand-written scanners over the shared literal set, the ceiling the Oak
// matcher is measured against:
//   memmem : one libc memmem sweep per literal (the naive baseline)
//   teddy  : a Teddy-style SIMD prefilter (Hyperscan's multi-literal
//            prefilter): literals are hashed into eight buckets by id; for
//            each of the first two bytes of every literal, a low-nibble and a
//            high-nibble table of bucket masks; per sixteen-byte block, two
//            table lookups per byte position (NEON tbl) ANDed give the
//            buckets whose byte 0 matches at each position, the same over
//            the block shifted by one byte gives byte 1; positions where the
//            two agree are candidates, verified with memcmp against the
//            bucket's literals. Every read is within the input plus its
//            zeroed 64-byte pad; every verification is bounded by the length.
// Build: cc -std=c11 -O2 -o scan_c scan_c.c
#include <string.h>
#include "timing.h"
#include "literals.h"
#if defined(__aarch64__)
#include <arm_neon.h>
#endif

static size_t LENS[NLITERALS];

static uint64_t scan_memmem(const uint8_t *buf, uint64_t n) {
    uint64_t count = 0;
    for (unsigned j = 0; j < NLITERALS; j++) {
        const uint8_t *p = buf, *end = buf + n;
        for (;;) {
            const uint8_t *q = memmem(p, (size_t)(end - p), LITERALS[j], LENS[j]);
            if (!q) break;
            count++; p = q + 1;
        }
    }
    return count;
}

#if defined(__aarch64__)
static uint8_t LO0[16], HI0[16], LO1[16], HI1[16];
static void teddy_build(void) {
    for (unsigned j = 0; j < NLITERALS; j++) {
        uint8_t bit = (uint8_t)(1u << (j % 8));
        uint8_t c0 = (uint8_t)LITERALS[j][0], c1 = (uint8_t)LITERALS[j][1];
        LO0[c0 & 15] |= bit; HI0[c0 >> 4] |= bit;
        LO1[c1 & 15] |= bit; HI1[c1 >> 4] |= bit;
    }
}
static uint64_t scan_teddy(const uint8_t *buf, uint64_t n) {
    const uint8x16_t lo0 = vld1q_u8(LO0), hi0 = vld1q_u8(HI0), lo1 = vld1q_u8(LO1), hi1 = vld1q_u8(HI1);
    const uint8x16_t nib = vdupq_n_u8(0x0F);
    uint64_t count = 0;
    for (uint64_t i = 0; i < n; i += 16) {
        uint8x16_t b0 = vld1q_u8(buf + i), b1 = vld1q_u8(buf + i + 1);
        uint8x16_t m0 = vandq_u8(vqtbl1q_u8(lo0, vandq_u8(b0, nib)), vqtbl1q_u8(hi0, vshrq_n_u8(b0, 4)));
        uint8x16_t m1 = vandq_u8(vqtbl1q_u8(lo1, vandq_u8(b1, nib)), vqtbl1q_u8(hi1, vshrq_n_u8(b1, 4)));
        uint8x16_t cand = vandq_u8(m0, m1);
        if (vmaxvq_u8(cand) == 0) continue;
        uint8_t c[16]; vst1q_u8(c, cand);
        for (unsigned l = 0; l < 16; l++) {
            if (!c[l]) continue;
            uint64_t pos = i + l;
            for (unsigned j = 0; j < NLITERALS; j++) {
                if (!(c[l] & (1u << (j % 8)))) continue;
                if (pos + LENS[j] <= n && memcmp(buf + pos, LITERALS[j], LENS[j]) == 0) count++;
            }
        }
    }
    return count;
}

// Three-byte prefilter over sixty-four-byte steps: four blocks per
// iteration, the candidates of all four ORed before any is examined, so a
// clean 64 bytes costs the lookups and one test. Byte 2 exists for every
// literal (the shortest is four bytes).
static uint8_t LO2[16], HI2[16];
static void teddy3_build(void) {
    for (unsigned j = 0; j < NLITERALS; j++) {
        uint8_t bit = (uint8_t)(1u << (j % 8));
        uint8_t c2 = (uint8_t)LITERALS[j][2];
        LO2[c2 & 15] |= bit; HI2[c2 >> 4] |= bit;
    }
}
static inline uint8x16_t teddy_lookup(uint8x16_t lo, uint8x16_t hi, uint8x16_t nib, uint8x16_t b) {
    return vandq_u8(vqtbl1q_u8(lo, vandq_u8(b, nib)), vqtbl1q_u8(hi, vshrq_n_u8(b, 4)));
}
static uint64_t teddy_verify(const uint8_t *buf, uint64_t n, uint64_t base, uint8x16_t cand) {
    uint64_t count = 0; uint8_t c[16]; vst1q_u8(c, cand);
    for (unsigned l = 0; l < 16; l++) {
        if (!c[l]) continue;
        uint64_t pos = base + l;
        for (unsigned j = 0; j < NLITERALS; j++) {
            if (!(c[l] & (1u << (j % 8)))) continue;
            if (pos + LENS[j] <= n && memcmp(buf + pos, LITERALS[j], LENS[j]) == 0) count++;
        }
    }
    return count;
}
static uint64_t scan_teddy3(const uint8_t *buf, uint64_t n) {
    const uint8x16_t lo0 = vld1q_u8(LO0), hi0 = vld1q_u8(HI0), lo1 = vld1q_u8(LO1), hi1 = vld1q_u8(HI1), lo2 = vld1q_u8(LO2), hi2 = vld1q_u8(HI2);
    const uint8x16_t nib = vdupq_n_u8(0x0F);
    uint64_t count = 0, i = 0;
    for (; i + 64 <= n; i += 64) {
        uint8x16_t cand[4]; uint8x16_t any = vdupq_n_u8(0);
        for (unsigned k = 0; k < 4; k++) {
            const uint8_t *p = buf + i + 16 * k;
            uint8x16_t m0 = teddy_lookup(lo0, hi0, nib, vld1q_u8(p));
            uint8x16_t m1 = teddy_lookup(lo1, hi1, nib, vld1q_u8(p + 1));
            uint8x16_t m2 = teddy_lookup(lo2, hi2, nib, vld1q_u8(p + 2));
            cand[k] = vandq_u8(vandq_u8(m0, m1), m2);
            any = vorrq_u8(any, cand[k]);
        }
        if (vmaxvq_u8(any) == 0) continue;
        for (unsigned k = 0; k < 4; k++) if (vmaxvq_u8(cand[k])) count += teddy_verify(buf, n, i + 16 * k, cand[k]);
    }
    for (; i < n; i += 16) {
        const uint8_t *p = buf + i;
        uint8x16_t cand = vandq_u8(vandq_u8(teddy_lookup(lo0, hi0, nib, vld1q_u8(p)), teddy_lookup(lo1, hi1, nib, vld1q_u8(p + 1))), teddy_lookup(lo2, hi2, nib, vld1q_u8(p + 2)));
        if (vmaxvq_u8(cand)) count += teddy_verify(buf, n, i, cand);
    }
    return count;
}
#endif

int main(void) {
    uint64_t n; uint8_t *buf = read_input(&n);
    memset(buf + n, 0, 64);
    for (unsigned j = 0; j < NLITERALS; j++) LENS[j] = strlen(LITERALS[j]);
    double best_m = 1e30; uint64_t cm = 0;
    for (int r = 0; r < 5; r++) { double t0 = now_ns(); cm = scan_memmem(buf, n); double t = now_ns() - t0; if (t < best_m) best_m = t; }
    REPORT("memmem per literal (libc)", best_m, n);
    printf("   matches %llu\n", (unsigned long long)cm);
#if defined(__aarch64__)
    teddy_build();
    double best_t = 1e30; uint64_t ct = 0;
    for (int r = 0; r < 5; r++) { double t0 = now_ns(); ct = scan_teddy(buf, n); double t = now_ns() - t0; if (t < best_t) best_t = t; }
    REPORT("Teddy-style NEON prefilter, C", best_t, n);
    printf("   matches %llu\n", (unsigned long long)ct);
    if (ct != cm) { printf("MISMATCH\n"); return 1; }
    teddy3_build();
    double best_3 = 1e30; uint64_t c3 = 0;
    for (int r = 0; r < 5; r++) { double t0 = now_ns(); c3 = scan_teddy3(buf, n); double t = now_ns() - t0; if (t < best_3) best_3 = t; }
    REPORT("Teddy 3-byte, 64-byte steps, C", best_3, n);
    printf("   matches %llu\n", (unsigned long long)c3);
    if (c3 != cm) { printf("MISMATCH\n"); return 1; }
#endif
    free(buf);
    return 0;
}
