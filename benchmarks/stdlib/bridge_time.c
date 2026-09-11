/* time: RFC 3339 with nine fraction digits at offset zero. */
#define main oak_bench_unused_main
#include "oak_time.c"
#undef main
#include "runner.h"

static size_t instant_count;
static int64_t *instants;
static uint8_t *rfc_text, *rfc_reference;
static size_t rfc_length;

static void time_setup(double scale) {
  instant_count = bench_scaled(scale, 1000000);
  instants = bench_alloc(instant_count * sizeof *instants);
  rfc_text = bench_alloc(instant_count * 30);
  rfc_reference = bench_alloc(instant_count * 30);
  bench_fill_instants(instants, instant_count, 10);
  oak_view_i64 nanos = { instants, (u32)instant_count };
  oak_span_u8 dst = { rfc_reference, (u32)(instant_count * 30) };
  rfc_length = oak_bench_format_rfc3339(nanos, dst);
  if (!rfc_length) { fprintf(stderr, "time setup failed\n"); exit(1); }
  for (int i = 0; i < 2; ++i) { bench_workloads[i].items = instant_count; bench_workloads[i].bytes = rfc_length; }
}

static uint64_t run_format(int backend) {
  (void)backend;
  oak_view_i64 nanos = { instants, (u32)instant_count };
  oak_span_u8 dst = { rfc_text, (u32)(instant_count * 30) };
  u32 n = oak_bench_format_rfc3339(nanos, dst);
  return bench_fnv_bytes(rfc_text, n);
}

static uint64_t run_parse(int backend) {
  (void)backend;
  oak_view_u8 src = { rfc_reference, (u32)rfc_length };
  return oak_bench_parse_rfc3339(src, (u32)instant_count);
}

BenchWorkload bench_workloads[] = {
  { "time/format_rfc3339", { "oak" }, 1, time_setup, run_format, 0, 0 },
  { "time/parse_rfc3339", { "oak" }, 1, time_setup, run_parse, 0, 0 },
};
const int bench_workload_count = 2;
