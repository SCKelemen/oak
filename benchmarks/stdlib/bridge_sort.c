/* sort: Oak sort_span[u32] against libc qsort on the same corpora. The
   generated C is kept in this translation unit; its main is renamed away. */
#define main oak_bench_unused_main
#include "oak_sort.c"
#undef main
#include "runner.h"

static size_t sort_count;
static uint32_t *sort_random, *sort_sorted, *sort_reversed, *sort_work;

static int compare_u32(const void *a, const void *b) {
  uint32_t x = *(const uint32_t *)a, y = *(const uint32_t *)b;
  return x < y ? -1 : x > y;
}

static void sort_setup(double scale) {
  sort_count = bench_scaled(scale, 100000);
  sort_random = bench_alloc(sort_count * sizeof *sort_random);
  sort_sorted = bench_alloc(sort_count * sizeof *sort_sorted);
  sort_reversed = bench_alloc(sort_count * sizeof *sort_reversed);
  sort_work = bench_alloc(sort_count * sizeof *sort_work);
  bench_fill_u32(sort_random, sort_count, 1);
  memcpy(sort_sorted, sort_random, sort_count * sizeof *sort_sorted);
  qsort(sort_sorted, sort_count, sizeof *sort_sorted, compare_u32);
  for (size_t i = 0; i < sort_count; ++i) sort_reversed[i] = sort_sorted[sort_count - 1 - i];
  for (int i = 0; i < bench_workload_count; ++i) {
    bench_workloads[i].items = sort_count;
    bench_workloads[i].bytes = sort_count * sizeof(uint32_t);
  }
}

/* The copy of the input is inside the timed region for every backend. */
static uint64_t sort_run(const uint32_t *input, int backend) {
  memcpy(sort_work, input, sort_count * sizeof *sort_work);
  if (backend == 0) {
    oak_span_u32 items = { sort_work, (u32)sort_count };
    oak_bench_sort(items);
    oak_view_u32 sorted = { sort_work, (u32)sort_count };
    if (oak_bench_is_sorted(sorted) != oak_Bool_True) return 0;
  } else {
    qsort(sort_work, sort_count, sizeof *sort_work, compare_u32);
  }
  return bench_fnv_u32(sort_work, sort_count);
}

static void setup_all(double scale) { sort_setup(scale); }
static uint64_t run_random(int backend) { return sort_run(sort_random, backend); }
static uint64_t run_sorted(int backend) { return sort_run(sort_sorted, backend); }
static uint64_t run_reversed(int backend) { return sort_run(sort_reversed, backend); }

BenchWorkload bench_workloads[] = {
  { "sort/random", { "oak", "c_qsort" }, 2, setup_all, run_random, 0, 0 },
  { "sort/sorted", { "oak", "c_qsort" }, 2, setup_all, run_sorted, 0, 0 },
  { "sort/reversed", { "oak", "c_qsort" }, 2, setup_all, run_reversed, 0, 0 },
};
const int bench_workload_count = 3;
