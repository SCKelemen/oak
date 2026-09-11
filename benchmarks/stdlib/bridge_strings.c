/* strings: UTF-8 validation and scanning, decimal parsing and formatting. */
#define main oak_bench_unused_main
#include "oak_strings.c"
#undef main
#include "runner.h"

static size_t utf8_length, decimal_count, decimal_text_length;
static uint8_t *utf8_text, *decimal_text, *decimal_out;
static uint64_t *decimal_values;

static void strings_setup(double scale) {
  size_t capacity = bench_scaled(scale, 32u << 20);
  utf8_text = bench_alloc(capacity);
  utf8_length = bench_fill_utf8(utf8_text, capacity, 8);
  decimal_count = bench_scaled(scale, 1000000);
  decimal_values = bench_alloc(decimal_count * sizeof *decimal_values);
  bench_fill_decimals(decimal_values, decimal_count, 9);
  decimal_text = bench_alloc(decimal_count * 21);
  decimal_out = bench_alloc(decimal_count * 21);
  decimal_text_length = bench_write_decimals(decimal_text, decimal_values, decimal_count);
  bench_workloads[0].items = utf8_length; bench_workloads[0].bytes = utf8_length;
  bench_workloads[1].items = utf8_length; bench_workloads[1].bytes = utf8_length;
  bench_workloads[2].items = decimal_count; bench_workloads[2].bytes = decimal_text_length;
  bench_workloads[3].items = decimal_count; bench_workloads[3].bytes = decimal_text_length;
}

static uint64_t run_validate(int backend) {
  (void)backend;
  oak_view_u8 src = { utf8_text, (u32)utf8_length };
  return oak_bench_utf8_validate(src) == oak_Bool_True ? 1 : 0;
}

static uint64_t run_scan(int backend) {
  (void)backend;
  oak_view_u8 src = { utf8_text, (u32)utf8_length };
  return oak_bench_utf8_scan(src);
}

static uint64_t run_parse(int backend) {
  (void)backend;
  oak_view_u8 src = { decimal_text, (u32)decimal_text_length };
  return oak_bench_parse_u64(src);
}

static uint64_t run_append(int backend) {
  (void)backend;
  oak_view_u64 values = { decimal_values, (u32)decimal_count };
  oak_span_u8 dst = { decimal_out, (u32)(decimal_count * 21) };
  u32 n = oak_bench_append_u64(values, dst);
  return bench_fnv_bytes(decimal_out, n);
}

BenchWorkload bench_workloads[] = {
  { "strings/utf8_validate", { "oak" }, 1, strings_setup, run_validate, 0, 0 },
  { "strings/utf8_scan", { "oak" }, 1, strings_setup, run_scan, 0, 0 },
  { "strings/parse_u64", { "oak" }, 1, strings_setup, run_parse, 0, 0 },
  { "strings/append_u64", { "oak" }, 1, strings_setup, run_append, 0, 0 },
};
const int bench_workload_count = 4;
