// State-machine lowering benchmark: which code shape steps a machine fastest
// on today's hardware when the step stream is input-driven (unpredictable)?
//
// Three workloads:
//   A. one small control machine (VirtualIrq: 3 states, 4 steps), 64M steps
//   B. one byte-driven DFA (UTF-8 validity, 9 states, 256 symbols), 64MB
//   C. a table of 1M machines, each stepped once per round, 32 rounds
//
// Variants per workload:
//   branch : the branch tree clang produces from Oak's generated C today
//   table  : dense u8 next[state][step] with an illegal sentinel, one load
//   shift  : Vognsen-style shift DFA, one u64 row per symbol, state as a
//            6-bit field offset: next = (row[sym] >> state) & 63
//
// Build: cc -std=c11 -O2 -o bench bench.c ; run: ./bench
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef uint8_t u8; typedef uint32_t u32; typedef uint64_t u64;

static double now_ns(void) {
    struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec * 1e9 + (double)ts.tv_nsec;
}
static u64 rng_state = 0x9E3779B97F4A7C15ull;
static inline u32 rng(void) { // xorshift64*
    u64 x = rng_state; x ^= x >> 12; x ^= x << 25; x ^= x >> 27; rng_state = x;
    return (u32)((x * 0x2545F4914F6CDD1Dull) >> 32);
}
#define REPS 5
static double best(double a, double b) { return a < b ? a : b; }

/* ------------------------------------------------------------------ */
/* A. VirtualIrq: Idle=0 Pending=1 Active=2; Inject=0 Ack=1 Eoi=2 Program=3 */
enum { ST_IDLE, ST_PENDING, ST_ACTIVE, NSTATES_A = 3 };
enum { STEP_INJECT, STEP_ACK, STEP_EOI, STEP_PROGRAM, NSTEPS_A = 4 };

// (1) branch: shape of Oak's generated C (assert(legal) then dispatch),
// which clang fuses into one tree. Reproduced faithfully.
static inline int a_legal(u32 state, u32 step) {
    if (step == STEP_INJECT) return state == ST_IDLE;
    if (step == STEP_ACK) return state == ST_PENDING;
    if (step == STEP_EOI) return state == ST_ACTIVE;
    if (step == STEP_PROGRAM) return state == ST_IDLE || state == ST_PENDING;
    __builtin_trap();
}
__attribute__((noinline)) static u32 a_next_branch(u32 state, u32 step) {
    if (!a_legal(state, step)) __builtin_trap();
    if (step == STEP_INJECT) { if (state == ST_IDLE) return ST_PENDING; return state; }
    if (step == STEP_ACK) { if (state == ST_PENDING) return ST_ACTIVE; return state; }
    if (step == STEP_EOI) { if (state == ST_ACTIVE) return ST_IDLE; return state; }
    if (step == STEP_PROGRAM) { return state; }
    __builtin_trap();
}
// (2) table
#define ILLEGAL 0xFF
static const u8 A_NEXT[NSTATES_A][NSTEPS_A] = {
    /* Idle    */ { ST_PENDING, ILLEGAL,   ILLEGAL, ST_IDLE },
    /* Pending */ { ILLEGAL,    ST_ACTIVE, ILLEGAL, ST_PENDING },
    /* Active  */ { ILLEGAL,    ILLEGAL,   ST_IDLE, ILLEGAL },
};
static inline u32 a_next_table(u32 state, u32 step) {
    u32 n = A_NEXT[state][step];
    if (__builtin_expect(n == ILLEGAL, 0)) __builtin_trap();
    return n;
}
// (3) shift DFA: state s is the bit offset 6*s; row[step] packs next(s, step)
// for every s in 6-bit fields; illegal -> sink 63 (absorbing, checked at end
// of the batch: the sink is reachable only through an illegal pair).
static u64 A_ROW[NSTEPS_A];
#define A_SINK NSTATES_A   /* absorbing illegal state, offset 6*A_SINK = 18 */
static void a_build_rows(void) {
    for (u32 step = 0; step < NSTEPS_A; step++) {
        u64 row = 0;
        for (u32 s = 0; s <= NSTATES_A; s++) {
            u64 n = A_SINK;
            if (s < NSTATES_A && A_NEXT[s][step] != ILLEGAL) n = A_NEXT[s][step];
            row |= (n * 6) << (6 * s);   /* fields hold the NEXT OFFSET directly */
        }
        A_ROW[step] = row;
    }
}
static inline u32 a_next_shift(u32 off, u32 step) { /* off = 6*state; returns 6*state' */
    return (u32)((A_ROW[step] >> off) & 63);
}

static void bench_a(u32 n) {
    u8 *steps = malloc(n);
    // random walk over legal steps so the branch version never traps
    static const u8 legal_from[NSTATES_A][2] = { {STEP_INJECT, STEP_PROGRAM}, {STEP_ACK, STEP_PROGRAM}, {STEP_EOI, STEP_EOI} };
    u32 s = ST_IDLE;
    for (u32 i = 0; i < n; i++) { u8 st = legal_from[s][rng() & 1]; steps[i] = st; s = A_NEXT[s][st]; }
    a_build_rows();
    double tb = 1e30, tt = 1e30, ts = 1e30; u32 rb = 0, rt = 0, rs = 0;
    for (int r = 0; r < REPS; r++) {
        double t0 = now_ns(); u32 st = ST_IDLE;
        for (u32 i = 0; i < n; i++) st = a_next_branch(st, steps[i]);
        tb = best(tb, now_ns() - t0); rb = st;
        t0 = now_ns(); st = ST_IDLE;
        for (u32 i = 0; i < n; i++) st = a_next_table(st, steps[i]);
        tt = best(tt, now_ns() - t0); rt = st;
        t0 = now_ns(); u32 off = 0;
        for (u32 i = 0; i < n; i++) off = a_next_shift(off, steps[i]);
        if (off == 6 * A_SINK) __builtin_trap();
        ts = best(ts, now_ns() - t0); rs = off / 6;
    }
    if (rb != rt || rt != rs) { printf("A: MISMATCH %u %u %u\n", rb, rt, rs); exit(1); }
    printf("A  single control machine, %u input-driven steps\n", n);
    printf("   branch  %6.2f ns/step\n   table   %6.2f ns/step\n   shift   %6.2f ns/step\n", tb / n, tt / n, ts / n);
    free(steps);
}

/* ------------------------------------------------------------------ */
/* B. UTF-8 validity DFA: 9 states (0 accept, 1..7 continuation classes,
   8 = reject/sink). Classic Bjoern Hoehrmann-style class table + state table. */
static const u8 U8_CLASS[256] = {
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1, 9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,
  7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7, 7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,
  8,8,2,2,2,2,2,2,2,2,2,2,2,2,2,2, 2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,
 10,3,3,3,3,3,3,3,3,3,3,3,3,4,3,3, 11,6,6,6,5,8,8,8,8,8,8,8,8,8,8,8,
};
// Hoehrmann's transition table over 12 classes, 9 states (scaled by 12 in the
// original; here as explicit [state][class]).
static const u8 U8_NEXT[9][12] = {
 /* 0 accept */ {0,12>0?1:1, 2,3,5,8,7,1,1,1,4,6},
 // The above line is a placeholder that gets overwritten by u8_build().
};
static u8 U8_T[9][12];
static void u8_build(void) {
    // Standard Hoehrmann table, states multiplied out (accept=0, reject=1 -> we use 8 as sink)
    static const u8 h[108] = {
      0,12,24,36,60,96,84,12,12,12,48,72,
      12,12,12,12,12,12,12,12,12,12,12,12,
      12, 0,12,12,12,12,12, 0,12, 0,12,12,
      12,24,12,12,12,12,12,24,12,24,12,12,
      12,12,12,12,12,12,12,24,12,12,12,12,
      12,24,12,12,12,12,12,12,12,24,12,12,
      12,12,12,12,12,12,12,36,12,36,12,12,
      12,36,12,12,12,12,12,36,12,36,12,12,
      12,36,12,12,12,12,12,12,12,12,12,12,
    };
    for (int s = 0; s < 9; s++) for (int c = 0; c < 12; c++) {
        u8 v = h[s * 12 + c] / 12; // 0..8 ; 1 == reject in Hoehrmann's numbering
        U8_T[s][c] = v;
    }
}
__attribute__((noinline)) static u32 b_run_branch(const u8 *p, u32 n) {
    // Nested if/else over class and state — the shape a match-lowering produces.
    u32 s = 0;
    for (u32 i = 0; i < n; i++) {
        u32 c = U8_CLASS[p[i]];
        // emulate a branch tree over the (state, class) pair
        u32 nx;
        if (s == 0) { nx = U8_T[0][c]; }
        else if (s == 1) { nx = 1; }
        else if (s == 2) { nx = (c == 1 || c == 7 || c == 9) ? 0 : 1; }
        else if (s == 3) { nx = (c == 1 || c == 7 || c == 9) ? 2 : 1; }
        else if (s == 4) { nx = (c == 7) ? 2 : 1; }
        else if (s == 5) { nx = (c == 1 || c == 9) ? 2 : 1; }
        else if (s == 6) { nx = (c == 7 || c == 9) ? 3 : 1; }
        else if (s == 7) { nx = (c == 1 || c == 7 || c == 9) ? 3 : 1; }
        else { nx = (c == 1) ? 3 : 1; }
        s = nx;
    }
    return s;
}
__attribute__((noinline)) static u32 b_run_table(const u8 *p, u32 n) {
    u32 s = 0;
    for (u32 i = 0; i < n; i++) s = U8_T[s][U8_CLASS[p[i]]];
    return s;
}
// merged 256-symbol table: next[state][byte], 9*256 = 2304 bytes, one load per byte
static u8 U8_FULL[9][256];
__attribute__((noinline)) static u32 b_run_fulltable(const u8 *p, u32 n) {
    u32 s = 0;
    for (u32 i = 0; i < n; i++) s = U8_FULL[s][p[i]];
    return s;
}
// shift DFA: one u64 per byte; 9 states * 6 bits = 54 bits
static u64 U8_ROW[256];
__attribute__((noinline)) static u32 b_run_shift(const u8 *p, u32 n) {
    u64 off = 0;
    for (u32 i = 0; i < n; i++) off = (U8_ROW[p[i]] >> off) & 63;
    return (u32)off / 6;
}
static void bench_b(u32 n) {
    u8_build();
    for (int s = 0; s < 9; s++) for (int b = 0; b < 256; b++) U8_FULL[s][b] = U8_T[s][U8_CLASS[b]];
    for (int b = 0; b < 256; b++) { u64 row = 0; for (int s = 0; s < 9; s++) row |= (u64)(U8_FULL[s][b] * 6) << (6 * s); U8_ROW[b] = row; }
    // input: random mix of ASCII (70%) and random bytes (30%) — unpredictable classes
    u8 *buf = malloc(n + 4);
    { u32 i = 0;
      while (i + 4 <= n) {
        u32 r = rng(); u32 kind = r % 10; u32 cp;
        if (kind < 6) cp = 32 + (r >> 8) % 95;                 /* ASCII */
        else if (kind < 8) cp = 0x80 + (r >> 8) % (0x800 - 0x80); /* 2-byte */
        else if (kind < 9) { cp = 0x800 + (r >> 8) % (0xFFFF - 0x800); if (cp >= 0xD800 && cp <= 0xDFFF) cp = 0x4E00; } /* 3-byte */
        else cp = 0x10000 + (r >> 8) % (0x10FFFF - 0x10000);  /* 4-byte */
        if (cp < 0x80) buf[i++] = (u8)cp;
        else if (cp < 0x800) { buf[i++] = (u8)(0xC0 | (cp >> 6)); buf[i++] = (u8)(0x80 | (cp & 63)); }
        else if (cp < 0x10000) { buf[i++] = (u8)(0xE0 | (cp >> 12)); buf[i++] = (u8)(0x80 | ((cp >> 6) & 63)); buf[i++] = (u8)(0x80 | (cp & 63)); }
        else { buf[i++] = (u8)(0xF0 | (cp >> 18)); buf[i++] = (u8)(0x80 | ((cp >> 12) & 63)); buf[i++] = (u8)(0x80 | ((cp >> 6) & 63)); buf[i++] = (u8)(0x80 | (cp & 63)); }
      }
      while (i < n) buf[i++] = 'a';
    }
    double tb = 1e30, tt = 1e30, tf = 1e30, ts = 1e30; u32 rb = 0, rt = 0, rf = 0, rs = 0;
    for (int r = 0; r < REPS; r++) {
        double t0 = now_ns(); rb = b_run_branch(buf, n); tb = best(tb, now_ns() - t0);
        t0 = now_ns(); rt = b_run_table(buf, n); tt = best(tt, now_ns() - t0);
        t0 = now_ns(); rf = b_run_fulltable(buf, n); tf = best(tf, now_ns() - t0);
        t0 = now_ns(); rs = b_run_shift(buf, n); ts = best(ts, now_ns() - t0);
    }
    if (rb != rt || rt != rf || rf != rs) { printf("B: MISMATCH %u %u %u %u\n", rb, rt, rf, rs); exit(1); }
    printf("B  byte-driven DFA (UTF-8 classes, 9 states), %u bytes\n", n);
    printf("   branch       %6.2f ns/byte  (%.2f GB/s)\n", tb / n, n / tb);
    printf("   class+table  %6.2f ns/byte  (%.2f GB/s)\n", tt / n, n / tt);
    printf("   full table   %6.2f ns/byte  (%.2f GB/s)\n", tf / n, n / tf);
    printf("   shift        %6.2f ns/byte  (%.2f GB/s)\n", ts / n, n / ts);
    free(buf);
}

/* ------------------------------------------------------------------ */
/* C. 1M independent VirtualIrq machines, one step each per round. */
static void bench_c(u32 m, u32 rounds) {
    u8 *soa = calloc(m, 1);           // SoA u8 state per machine
    u32 *aos = calloc(m, 4);          // u32 tag per machine, as today's ADT
    u8 *steps = malloc((size_t)m * rounds);
    static const u8 legal_from[NSTATES_A][2] = { {STEP_INJECT, STEP_PROGRAM}, {STEP_ACK, STEP_PROGRAM}, {STEP_EOI, STEP_EOI} };
    { // legal step per machine per round, from a simulated walk
        u8 *sim = calloc(m, 1);
        for (u32 r = 0; r < rounds; r++) for (u32 i = 0; i < m; i++) { u8 st = legal_from[sim[i]][rng() & 1]; steps[(size_t)r * m + i] = st; sim[i] = A_NEXT[sim[i]][st]; }
        free(sim);
    }
    double tb = 1e30, tt = 1e30, tt32 = 1e30;
    u64 cb = 0, ct = 0, ct32 = 0;
    for (int rep = 0; rep < REPS; rep++) {
        memset(aos, 0, (size_t)m * 4);
        double t0 = now_ns();
        for (u32 r = 0; r < rounds; r++) { const u8 *st = steps + (size_t)r * m; for (u32 i = 0; i < m; i++) aos[i] = a_next_branch(aos[i], st[i]); }
        tb = best(tb, now_ns() - t0); cb = 0; for (u32 i = 0; i < m; i++) cb += aos[i];
        memset(soa, 0, m);
        t0 = now_ns();
        for (u32 r = 0; r < rounds; r++) { const u8 *st = steps + (size_t)r * m; for (u32 i = 0; i < m; i++) soa[i] = (u8)a_next_table(soa[i], st[i]); }
        tt = best(tt, now_ns() - t0); ct = 0; for (u32 i = 0; i < m; i++) ct += soa[i];
        memset(aos, 0, (size_t)m * 4);
        t0 = now_ns();
        for (u32 r = 0; r < rounds; r++) { const u8 *st = steps + (size_t)r * m; for (u32 i = 0; i < m; i++) aos[i] = a_next_table(aos[i], st[i]); }
        tt32 = best(tt32, now_ns() - t0); ct32 = 0; for (u32 i = 0; i < m; i++) ct32 += aos[i];
    }
    if (cb != ct || ct != ct32) { printf("C: MISMATCH\n"); exit(1); }
    double n = (double)m * rounds;
    printf("C  %u machines x %u rounds, one input-driven step each\n", m, rounds);
    printf("   branch, u32 tags  %6.2f ns/step\n   table,  u8 tags   %6.2f ns/step\n   table,  u32 tags  %6.2f ns/step\n", tb / n, tt / n, tt32 / n);
    free(soa); free(aos); free(steps);
}

int main(void) {
    bench_a(64u << 20);
    bench_b(64u << 20);
    bench_c(1u << 20, 32);
    bench_c(16u << 20, 4);
    return 0;
}
