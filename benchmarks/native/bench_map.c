// Times the element-wise span maps of map_add.oak as one backend emitted
// them: KERNEL_C names the emitted C (the native companion object linked
// beside it), LABEL the row. 2^20 elements, two hundred calls a round,
// best of seven rounds; every row prints its checksum. Build: run_map.sh.
#define main oak_program_main
#include KERNEL_C
#undef main
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
static double now_ns(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return (double)ts.tv_sec * 1e9 + (double)ts.tv_nsec; }
enum { N = 1 << 20, CALLS = 200, ROUNDS = 7 };
static double best_of(void (*run)(void)) {
    double best = 1e30;
    for (int r = 0; r < ROUNDS; r++) { double t0 = now_ns(); for (int c = 0; c < CALLS; c++) run(); double t = (now_ns() - t0) / CALLS; if (t < best) best = t; }
    return best;
}
static u32 *A, *B, *D; static f32 *FA, *FD;
static oak_span_u32 dst; static oak_view_u32 a, b; static oak_span_f32 fdst; static oak_view_f32 fa;
static void run_add_k(void) { oak_add_k(dst, a, 3u); }
static void run_bump(void) { oak_bump(dst, 1u); }
static void run_fmadd_k(void) { oak_fmadd_k(fdst, fa, 2.0f); }
static void run_sum_ab(void) { oak_sum_ab(dst, a, b); }
static unsigned long long sum_u32(const u32 *v) { unsigned long long s = 0; for (int i = 0; i < N; i++) s += v[i]; return s; }
static double sum_f32(const f32 *v) { double s = 0; for (int i = 0; i < N; i++) s += v[i]; return s; }
int main(void) {
    A = malloc(sizeof(u32) * N); B = malloc(sizeof(u32) * N); D = malloc(sizeof(u32) * N);
    FA = malloc(sizeof(f32) * N); FD = malloc(sizeof(f32) * N);
    if (!A || !B || !D || !FA || !FD) return 2;
    for (int i = 0; i < N; i++) { A[i] = (u32)i * 2654435761u; B[i] = (u32)i; D[i] = 0; FA[i] = (f32)i * 0.5f; FD[i] = 0; }
    dst.base = D; dst.len = N; a.base = A; a.len = N; b.base = B; b.len = N; fdst.base = FD; fdst.len = N; fa.base = FA; fa.len = N;
    double t;
    t = best_of(run_add_k); printf("%-22s add_k    %6.3f ns/element  checksum %llu\n", LABEL, t / N, sum_u32(D));
    for (int i = 0; i < N; i++) D[i] = A[i];
    t = best_of(run_bump); printf("%-22s bump     %6.3f ns/element  checksum %llu\n", LABEL, t / N, sum_u32(D));
    t = best_of(run_fmadd_k); printf("%-22s fmadd_k  %6.3f ns/element  checksum %.1f\n", LABEL, t / N, sum_f32(FD));
    t = best_of(run_sum_ab); printf("%-22s sum_ab   %6.3f ns/element  checksum %llu\n", LABEL, t / N, sum_u32(D));
    return 0;
}
