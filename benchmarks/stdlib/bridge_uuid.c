/* uuid: version 7 generation plus text formatting. */
#define main oak_bench_unused_main
#include "oak_uuid.c"
#undef main
#include "runner.h"

static size_t uuid_count;
static uint8_t *uuid_text;

static void uuid_setup(double scale) {
  uuid_count = bench_scaled(scale, 1000000);
  uuid_text = bench_alloc(uuid_count * 36);
  bench_workloads[0].items = uuid_count;
  bench_workloads[0].bytes = uuid_count * 36;
}

static uint64_t run_uuid(int backend) {
  (void)backend;
  oak_span_u8 dst = { uuid_text, (u32)(uuid_count * 36) };
  u32 n = oak_bench_uuid_v7_format(7, UINT64_C(1700000000000), (u32)uuid_count, dst);
  return bench_fnv_bytes(uuid_text, n);
}

BenchWorkload bench_workloads[] = {
  { "uuid/v7_format", { "oak" }, 1, uuid_setup, run_uuid, 0, 0 },
};
const int bench_workload_count = 1;
