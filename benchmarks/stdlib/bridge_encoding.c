/* encoding: base64, hex and percent codecs over random bytes. */
#define main oak_bench_unused_main
#include "oak_encoding.c"
#undef main
#include "runner.h"

static size_t raw_length, percent_length;
static uint8_t *raw, *base64_text, *hex_text, *decoded, *percent_raw, *percent_text;
static size_t base64_length, hex_length;

static void encoding_setup(double scale) {
  raw_length = bench_scaled(scale, 16u << 20);
  percent_length = bench_scaled(scale, 4u << 20);
  raw = bench_alloc(raw_length);
  base64_text = bench_alloc(raw_length / 3 * 4 + 8);
  hex_text = bench_alloc(raw_length * 2);
  decoded = bench_alloc(raw_length);
  percent_raw = bench_alloc(percent_length);
  percent_text = bench_alloc(percent_length * 3);
  bench_fill_bytes(raw, raw_length, 3);
  bench_fill_percent(percent_raw, percent_length, 4);
  oak_view_u8 src = { raw, (u32)raw_length };
  oak_span_u8 b64 = { base64_text, (u32)(raw_length / 3 * 4 + 8) };
  oak_span_u8 hex = { hex_text, (u32)(raw_length * 2) };
  base64_length = oak_bench_base64_encode(b64, src);
  hex_length = oak_bench_hex_encode(hex, src);
  if (!base64_length || !hex_length) { fprintf(stderr, "encoding setup failed\n"); exit(1); }
  for (int i = 0; i < 4; ++i) { bench_workloads[i].items = raw_length; bench_workloads[i].bytes = raw_length; }
  bench_workloads[4].items = percent_length;
  bench_workloads[4].bytes = percent_length;
}

static uint64_t run_base64_encode(int backend) {
  (void)backend;
  oak_view_u8 src = { raw, (u32)raw_length };
  oak_span_u8 dst = { base64_text, (u32)(raw_length / 3 * 4 + 8) };
  u32 n = oak_bench_base64_encode(dst, src);
  return bench_fnv_bytes(base64_text, n);
}

static uint64_t run_base64_decode(int backend) {
  (void)backend;
  oak_view_u8 src = { base64_text, (u32)base64_length };
  oak_span_u8 dst = { decoded, (u32)raw_length };
  u32 n = oak_bench_base64_decode(dst, src);
  return bench_fnv_bytes(decoded, n);
}

static uint64_t run_hex_encode(int backend) {
  (void)backend;
  oak_view_u8 src = { raw, (u32)raw_length };
  oak_span_u8 dst = { hex_text, (u32)(raw_length * 2) };
  u32 n = oak_bench_hex_encode(dst, src);
  return bench_fnv_bytes(hex_text, n);
}

static uint64_t run_hex_decode(int backend) {
  (void)backend;
  oak_view_u8 src = { hex_text, (u32)hex_length };
  oak_span_u8 dst = { decoded, (u32)raw_length };
  u32 n = oak_bench_hex_decode(dst, src);
  return bench_fnv_bytes(decoded, n);
}

static uint64_t run_percent_encode(int backend) {
  (void)backend;
  oak_view_u8 src = { percent_raw, (u32)percent_length };
  oak_view_u8 keep = { percent_raw, 0 };
  oak_span_u8 dst = { percent_text, (u32)(percent_length * 3) };
  u32 n = oak_bench_percent_encode(dst, src, keep);
  return bench_fnv_bytes(percent_text, n);
}

static void teardown(void) {
  free(raw); free(base64_text); free(hex_text); free(decoded); free(percent_raw); free(percent_text);
  raw = base64_text = hex_text = decoded = percent_raw = percent_text = NULL;
}

BenchWorkload bench_workloads[] = {
  { "encoding/base64_encode", { "oak" }, 1, encoding_setup, run_base64_encode, teardown, 0, 0 },
  { "encoding/base64_decode", { "oak" }, 1, encoding_setup, run_base64_decode, teardown, 0, 0 },
  { "encoding/hex_encode", { "oak" }, 1, encoding_setup, run_hex_encode, teardown, 0, 0 },
  { "encoding/hex_decode", { "oak" }, 1, encoding_setup, run_hex_decode, teardown, 0, 0 },
  { "encoding/percent_encode", { "oak" }, 1, encoding_setup, run_percent_encode, teardown, 0, 0 },
};
const int bench_workload_count = 5;
