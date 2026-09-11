/* normalize: NFC and NFD of a random UTF-8 corpus, and the NFC quick check
   over ASCII text (the decimal corpus). The output buffers are sized by the
   package's own `_size` functions before timing. */
#define main oak_bench_unused_main
#include "oak_normalize.c"
#undef main
#include "runner.h"

static size_t utf8_length, nfc_capacity, nfd_capacity, ascii_length;
static uint8_t *utf8_text, *nfc_out, *nfd_out, *ascii_text;

static void normalize_setup(double scale) {
  size_t capacity = bench_scaled(scale, 8u << 20);
  utf8_text = bench_alloc(capacity);
  utf8_length = bench_fill_utf8(utf8_text, capacity, 8);
  oak_view_u8 src = { utf8_text, (u32)utf8_length };
  nfc_capacity = oak_bench_nfc_size(src);
  nfd_capacity = oak_bench_nfd_size(src);
  nfc_out = bench_alloc(nfc_capacity ? nfc_capacity : 1);
  nfd_out = bench_alloc(nfd_capacity ? nfd_capacity : 1);
  size_t count = bench_scaled(scale, 1000000);
  uint64_t *values = bench_alloc(count * sizeof *values);
  bench_fill_decimals(values, count, 9);
  ascii_text = bench_alloc(count * 21);
  ascii_length = bench_write_decimals(ascii_text, values, count);
  free(values);
  bench_workloads[0].items = utf8_length; bench_workloads[0].bytes = utf8_length;
  bench_workloads[1].items = utf8_length; bench_workloads[1].bytes = utf8_length;
  bench_workloads[2].items = ascii_length; bench_workloads[2].bytes = ascii_length;
}

static uint64_t run_nfc(int backend) {
  (void)backend;
  oak_view_u8 src = { utf8_text, (u32)utf8_length };
  oak_span_u8 dst = { nfc_out, (u32)nfc_capacity };
  u32 n = oak_bench_nfc(dst, src);
  return bench_fnv_bytes(nfc_out, n);
}

static uint64_t run_nfd(int backend) {
  (void)backend;
  oak_view_u8 src = { utf8_text, (u32)utf8_length };
  oak_span_u8 dst = { nfd_out, (u32)nfd_capacity };
  u32 n = oak_bench_nfd(dst, src);
  return bench_fnv_bytes(nfd_out, n);
}

static uint64_t run_is_nfc(int backend) {
  (void)backend;
  oak_view_u8 src = { ascii_text, (u32)ascii_length };
  return oak_bench_is_nfc(src) == oak_Bool_True ? 1 : 0;
}

static void teardown(void) {
  free(utf8_text); free(nfc_out); free(nfd_out); free(ascii_text);
  utf8_text = nfc_out = nfd_out = ascii_text = NULL;
}

BenchWorkload bench_workloads[] = {
  { "normalize/nfc", { "oak" }, 1, normalize_setup, run_nfc, teardown, 0, 0 },
  { "normalize/nfd", { "oak" }, 1, normalize_setup, run_nfd, teardown, 0, 0 },
  { "normalize/is_nfc_ascii", { "oak" }, 1, normalize_setup, run_is_nfc, teardown, 0, 0 },
};
const int bench_workload_count = 3;
