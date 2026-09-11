/* hash: SHA-256 and CRC-32C over random bytes. */
#define main oak_bench_unused_main
#include "oak_hash.c"
#undef main
#include "runner.h"

static size_t hash_length;
static uint8_t *hash_input;

static void hash_setup(double scale) {
  hash_length = bench_scaled(scale, 32u << 20);
  hash_input = bench_alloc(hash_length);
  bench_fill_bytes(hash_input, hash_length, 5);
  for (int i = 0; i < 2; ++i) { bench_workloads[i].items = hash_length; bench_workloads[i].bytes = hash_length; }
}

static uint64_t run_sha256(int backend) {
  (void)backend;
  uint8_t digest[32];
  oak_view_u8 src = { hash_input, (u32)hash_length };
  oak_span_u8 out = { digest, 32 };
  if (oak_bench_sha256(src, out) != oak_Bool_True) return 0;
  return bench_fnv_bytes(digest, 32);
}

static uint64_t run_crc32c(int backend) {
  (void)backend;
  oak_view_u8 src = { hash_input, (u32)hash_length };
  return oak_bench_crc32c(src);
}

static void teardown(void) {
  free(hash_input);
  hash_input = NULL;
}

BenchWorkload bench_workloads[] = {
  { "hash/sha256", { "oak" }, 1, hash_setup, run_sha256, teardown, 0, 0 },
  { "hash/crc32c", { "oak" }, 1, hash_setup, run_crc32c, teardown, 0, 0 },
};
const int bench_workload_count = 2;
