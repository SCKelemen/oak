/* random: xoshiro256** draws folded with xor. */
#define main oak_bench_unused_main
#include "oak_random.c"
#undef main
#include "runner.h"

static uint64_t draw_count;

static void random_setup(double scale) {
  draw_count = bench_scaled(scale, 100000000);
  bench_workloads[0].items = draw_count;
  bench_workloads[0].bytes = draw_count * 8;
}

static uint64_t run_random(int backend) {
  (void)backend;
  return oak_bench_random(6, draw_count);
}

BenchWorkload bench_workloads[] = {
  { "random/xoshiro", { "oak" }, 1, random_setup, run_random, 0, 0 },
};
const int bench_workload_count = 1;
