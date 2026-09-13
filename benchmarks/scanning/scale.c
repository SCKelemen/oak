// How the Teddy scanner scales with the size of the literal set, and
// whether more buckets pay: sets of 16, 64, and 256 random lowercase
// literals (4 to 12 bytes, distinct) over 32 MB of random printable text
// with the literals planted about once per 4 KiB. Variants:
//   teddy8  : the kernel of literals.oak — eight buckets, three bytes
//   teddy16 : the same over two independent eight-bucket groups (the set
//             split in halves), two candidate masks per block: twice the
//             lookups, half the literals per bucket
//   groups  : one eight-bucket group per sixteen literals (two per bucket),
//             the candidate masks of every group ORed per block
//   hs      : Vectorscan's literal database on the same set
// Each reports ns/byte and the candidate lanes per MB the prefilter left
// to verification. Build: cc -std=c11 -O2 -I/opt/homebrew/opt/vectorscan/include -L/opt/homebrew/opt/vectorscan/lib -lhs -o scale scale.c
#include <hs/hs.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <arm_neon.h>
typedef uint8_t u8; typedef uint32_t u32; typedef uint64_t u64;
static double now_ns(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return (double)ts.tv_sec * 1e9 + (double)ts.tv_nsec; }
static u64 rng_state = 0x9E3779B97F4A7C15ull;
static inline u32 rng(void) { u64 x = rng_state; x ^= x >> 12; x ^= x << 25; x ^= x >> 27; rng_state = x; return (u32)((x * 0x2545F4914F6CDD1Dull) >> 32); }

#define MAXLIT 256
static char *LIT[MAXLIT]; static size_t LEN[MAXLIT]; static unsigned NLIT;

static void make_literals(unsigned n) {
    NLIT = n;
    for (unsigned j = 0; j < n; j++) {
        for (;;) {
            size_t len = 4 + rng() % 9;
            char *s = malloc(len + 1);
            for (size_t k = 0; k < len; k++) s[k] = (char)('a' + rng() % 26);
            s[len] = 0;
            int dup = 0;
            for (unsigned i = 0; i < j; i++) if (strcmp(LIT[i], s) == 0) { dup = 1; break; }
            if (dup) { free(s); continue; }
            LIT[j] = s; LEN[j] = len; break;
        }
    }
}
static u8 *make_text(u64 n, u64 *planted) {
    u8 *buf = malloc(n + 64); memset(buf + n, 0, 64);
    u64 i = 0, count = 0;
    while (i < n) {
        u32 r = rng();
        if (r % 4096 == 0) { unsigned j = (r >> 12) % NLIT; if (i + LEN[j] > n) break; memcpy(buf + i, LIT[j], LEN[j]); i += LEN[j]; count++; continue; }
        buf[i++] = (r % 80 == 0) ? '\n' : (u8)(32 + (r >> 8) % 95);
    }
    while (i < n) buf[i++] = '.';
    *planted = count; return buf;
}

/* a Teddy group: literals [first, first + count) in eight buckets, three bytes */
typedef struct { u8 lo[3][16], hi[3][16]; unsigned first, count; } Group;
static void group_build(Group *g, unsigned first, unsigned count) {
    memset(g, 0, sizeof *g); g->first = first; g->count = count;
    for (unsigned j = 0; j < count; j++) {
        u8 bit = (u8)(1u << (j % 8));
        for (int k = 0; k < 3; k++) { u8 c = (u8)LIT[first + j][k]; g->lo[k][c & 15] |= bit; g->hi[k][c >> 4] |= bit; }
    }
}
static inline uint8x16_t lookup(const Group *g, int k, uint8x16_t nib, uint8x16_t b) {
    return vandq_u8(vqtbl1q_u8(vld1q_u8(g->lo[k]), vandq_u8(b, nib)), vqtbl1q_u8(vld1q_u8(g->hi[k]), vshrq_n_u8(b, 4)));
}
static inline uint8x16_t classify(const Group *g, uint8x16_t nib, const u8 *p) {
    return vandq_u8(vandq_u8(lookup(g, 0, nib, vld1q_u8(p)), lookup(g, 1, nib, vld1q_u8(p + 1))), lookup(g, 2, nib, vld1q_u8(p + 2)));
}
static u64 verify(const Group *g, const u8 *buf, u64 n, u64 base, uint8x16_t cand, u64 *lanes) {
    u64 count = 0; u8 c[16]; vst1q_u8(c, cand);
    for (unsigned l = 0; l < 16; l++) {
        if (!c[l]) continue;
        (*lanes)++;
        u64 pos = base + l;
        for (unsigned j = 0; j < g->count; j++) {
            if (!(c[l] & (1u << (j % 8)))) continue;
            unsigned id = g->first + j;
            if (pos + LEN[id] <= n && memcmp(buf + pos, LIT[id], LEN[id]) == 0) count++;
        }
    }
    return count;
}
/* ngroups groups scanned together: per block, one candidate mask per group */
static u64 scan(const Group *groups, int ngroups, const u8 *buf, u64 n, u64 *lanes) {
    const uint8x16_t nib = vdupq_n_u8(0x0F);
    u64 count = 0, i = 0; *lanes = 0;
    for (; i + 66 <= n; i += 64) {
        uint8x16_t cand[16][4]; uint8x16_t any = vdupq_n_u8(0);
        for (int gi = 0; gi < ngroups; gi++)
            for (int k = 0; k < 4; k++) { cand[gi][k] = classify(&groups[gi], nib, buf + i + 16 * k); any = vorrq_u8(any, cand[gi][k]); }
        if (vmaxvq_u8(any) == 0) continue;
        for (int gi = 0; gi < ngroups; gi++)
            for (int k = 0; k < 4; k++) if (vmaxvq_u8(cand[gi][k])) count += verify(&groups[gi], buf, n, i + 16 * k, cand[gi][k], lanes);
    }
    for (; i < n; i++)
        for (unsigned j = 0; j < NLIT; j++) if (i + LEN[j] <= n && memcmp(buf + i, LIT[j], LEN[j]) == 0) count++;
    return count;
}

static u64 hs_count;
static int on_match(unsigned id, unsigned long long from, unsigned long long to, unsigned flags, void *ctx) { (void)id; (void)from; (void)to; (void)flags; (void)ctx; hs_count++; return 0; }

int main(void) {
    const u64 n = 32u << 20;
    unsigned sizes[3] = { 16, 64, 256 };
    printf("%-8s %-10s %10s %10s %14s %10s\n", "set", "variant", "ns/byte", "GB/s", "cand lanes/MB", "matches");
    for (int si = 0; si < 3; si++) {
        rng_state = 0x9E3779B97F4A7C15ull + sizes[si];
        make_literals(sizes[si]);
        u64 planted; u8 *buf = make_text(n, &planted);
        Group one; group_build(&one, 0, NLIT);
        Group two[2]; group_build(&two[0], 0, NLIT / 2); group_build(&two[1], NLIT / 2, NLIT - NLIT / 2);
        int ng = (NLIT + 15) / 16; Group many[16];
        for (int g = 0; g < ng; g++) group_build(&many[g], 16 * g, (16 * (g + 1) <= NLIT) ? 16 : NLIT - 16 * g);
        double best8 = 1e30, best16 = 1e30, bestg = 1e30, besths = 1e30; u64 c8 = 0, c16 = 0, cg = 0, l8 = 0, l16 = 0, lg = 0;
        for (int r = 0; r < 5; r++) {
            double t0 = now_ns(); c8 = scan(&one, 1, buf, n, &l8); double t = now_ns() - t0; if (t < best8) best8 = t;
            t0 = now_ns(); c16 = scan(two, 2, buf, n, &l16); t = now_ns() - t0; if (t < best16) best16 = t;
            t0 = now_ns(); cg = scan(many, ng, buf, n, &lg); t = now_ns() - t0; if (t < bestg) bestg = t;
        }
        unsigned flags[MAXLIT], ids[MAXLIT];
        for (unsigned j = 0; j < NLIT; j++) { flags[j] = 0; ids[j] = j; }
        hs_database_t *db = NULL; hs_compile_error_t *err = NULL;
        if (hs_compile_lit_multi((const char *const *)LIT, flags, ids, LEN, NLIT, HS_MODE_BLOCK, NULL, &db, &err) != HS_SUCCESS) { fprintf(stderr, "hs: %s\n", err->message); return 2; }
        hs_scratch_t *scratch = NULL; hs_alloc_scratch(db, &scratch);
        u64 chs = 0;
        for (int r = 0; r < 5; r++) { hs_count = 0; double t0 = now_ns(); hs_scan(db, (const char *)buf, (unsigned)n, 0, scratch, on_match, NULL); double t = now_ns() - t0; if (t < besths) besths = t; chs = hs_count; }
        printf("%-8u %-10s %10.2f %10.2f %14.0f %10llu\n", NLIT, "teddy8", best8 / n, n / best8, (double)l8 / (n / 1048576.0), (unsigned long long)c8);
        printf("%-8u %-10s %10.2f %10.2f %14.0f %10llu\n", NLIT, "teddy16", best16 / n, n / best16, (double)l16 / (n / 1048576.0), (unsigned long long)c16);
        char label[32]; snprintf(label, sizeof label, "groups%d", ng);
        printf("%-8u %-10s %10.2f %10.2f %14.0f %10llu\n", NLIT, label, bestg / n, n / bestg, (double)lg / (n / 1048576.0), (unsigned long long)cg);
        printf("%-8u %-10s %10.2f %10.2f %14s %10llu   (%llu planted)\n", NLIT, "vectorscan", besths / n, n / besths, "-", (unsigned long long)chs, (unsigned long long)planted);
        if (c8 != c16 || c8 != cg || c8 != chs) { printf("MISMATCH\n"); return 1; }
        hs_free_scratch(scratch); hs_free_database(db); free(buf);
        for (unsigned j = 0; j < NLIT; j++) free(LIT[j]);
    }
    return 0;
}
