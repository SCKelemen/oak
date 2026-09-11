/* varint: Oak LEB128 against a plain C loop. */
#define main oak_bench_unused_main
#include "oak_varint.c"
#undef main
#include "runner.h"

static size_t varint_count, varint_encoded_length;
static uint64_t *varint_values, *varint_decoded;
static uint8_t *varint_bytes, *varint_reference;

static size_t c_encode(uint8_t *dst, const uint64_t *values, size_t count) {
  size_t at = 0;
  for (size_t i = 0; i < count; ++i) {
    uint64_t v = values[i];
    while (v >= 0x80) { dst[at++] = (uint8_t)(v | 0x80); v >>= 7; }
    dst[at++] = (uint8_t)v;
  }
  return at;
}

static uint64_t c_decode(const uint8_t *src, size_t length, size_t count, uint64_t *out) {
  size_t at = 0;
  for (size_t i = 0; i < count; ++i) {
    uint64_t v = 0;
    unsigned shift = 0;
    for (;;) {
      if (at >= length || shift > 63) return 0;
      uint8_t b = src[at++];
      v |= (uint64_t)(b & 0x7F) << shift;
      if (!(b & 0x80)) break;
      shift += 7;
    }
    out[i] = v;
  }
  return at == length ? bench_fnv_u64(out, count) : 0;
}

static void varint_setup(double scale) {
  varint_count = bench_scaled(scale, 1000000);
  varint_values = bench_alloc(varint_count * sizeof *varint_values);
  varint_decoded = bench_alloc(varint_count * sizeof *varint_decoded);
  varint_bytes = bench_alloc(varint_count * 10);
  varint_reference = bench_alloc(varint_count * 10);
  bench_fill_varints(varint_values, varint_count, 2);
  varint_encoded_length = c_encode(varint_reference, varint_values, varint_count);
  bench_workloads[0].items = varint_count;
  bench_workloads[0].bytes = varint_encoded_length;
  bench_workloads[1].items = varint_count;
  bench_workloads[1].bytes = varint_encoded_length;
}

static uint64_t run_encode(int backend) {
  size_t written;
  if (backend == 0) {
    oak_view_u64 values = { varint_values, (u32)varint_count };
    oak_span_u8 dst = { varint_bytes, (u32)(varint_count * 10) };
    written = oak_bench_varint_encode(values, dst);
  } else {
    written = c_encode(varint_bytes, varint_values, varint_count);
  }
  if (written != varint_encoded_length) return 0;
  return bench_fnv_bytes(varint_bytes, written);
}

static uint64_t run_decode(int backend) {
  if (backend == 0) {
    oak_view_u8 src = { varint_reference, (u32)varint_encoded_length };
    return oak_bench_varint_decode(src, (u32)varint_count);
  }
  return c_decode(varint_reference, varint_encoded_length, varint_count, varint_decoded);
}

static void teardown(void) {
  free(varint_values); free(varint_decoded); free(varint_bytes); free(varint_reference);
  varint_values = varint_decoded = NULL;
  varint_bytes = varint_reference = NULL;
}

BenchWorkload bench_workloads[] = {
  { "varint/encode", { "oak", "c_loop" }, 2, varint_setup, run_encode, teardown, 0, 0 },
  { "varint/decode", { "oak", "c_loop" }, 2, varint_setup, run_decode, teardown, 0, 0 },
};
const int bench_workload_count = 2;
