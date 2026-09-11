/* The Oak side of the kernel comparison: one C runner around the generated
   program, with the same command line and output as the Go and Rust
   programs (benchmarks/kernels/README.md). */
#define main oak_kernels_unused_main
#include "kernels.c"
#undef main
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static uint64_t rng = 0x9E3779B97F4A7C15ull;
static uint64_t next_u64(void) {
  rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17;
  return rng;
}
static double now_ns(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (double)ts.tv_sec * 1e9 + (double)ts.tv_nsec;
}
static int cmp_double(const void *a, const void *b) {
  double x = *(const double *)a, y = *(const double *)b;
  return (x > y) - (x < y);
}

int main(int argc, char **argv) {
  if (argc != 5) { fprintf(stderr, "usage: runner KERNEL SIZE ROUNDS SAMPLES\n"); return 2; }
  const char *kernel = argv[1];
  uint32_t size = (uint32_t)strtoul(argv[2], NULL, 10);
  int rounds = atoi(argv[3]);
  int samples = atoi(argv[4]);
  uint8_t *bytes = malloc(size);
  float *fa = malloc(sizeof(float) * size), *fb = malloc(sizeof(float) * size);
  uint64_t *words = malloc(sizeof(uint64_t) * size);
  uint32_t probe_count = size / 16 == 0 ? 1 : size / 16;
  uint64_t *probes = malloc(sizeof(uint64_t) * probe_count);
  for (uint32_t i = 0; i < size; ++i) {
    uint64_t r = next_u64();
    bytes[i] = (uint8_t)r;
    fa[i] = (float)(r & 0xFFFF) / 65536.0f;
    fb[i] = (float)((r >> 16) & 0xFFFF) / 65536.0f;
    words[i] = (uint64_t)i * 3u;
  }
  for (uint32_t i = 0; i < probe_count; ++i) probes[i] = next_u64() % ((uint64_t)size * 3u + 3u);
  uint8_t out[32];
  double *ns = malloc(sizeof(double) * samples);
  char checksum[80] = "";
  for (int s = 0; s < samples; ++s) {
    double start = now_ns();
    uint64_t sink = 0;
    for (int r = 0; r < rounds; ++r) {
      if (!strcmp(kernel, "sha256")) {
        oak_view_u8 v = { bytes, size }; oak_span_u8 o = { out, 32 };
        oak_bench_sha256(v, o); sink += out[0];
      } else if (!strcmp(kernel, "blake3")) {
        oak_view_u8 v = { bytes, size }; oak_span_u8 o = { out, 32 };
        oak_bench_blake3(v, o); sink += out[0];
      } else if (!strcmp(kernel, "crc32c")) {
        oak_view_u8 v = { bytes, size };
        uint32_t c = oak_bench_crc32c(v); sink += c; memcpy(out, &c, 4);
      } else if (!strcmp(kernel, "dot")) {
        oak_view_f32 a = { fa, size }, b = { fb, size };
        float d = oak_bench_dot(a, b); memcpy(out, &d, 4); sink += out[0];
      } else if (!strcmp(kernel, "sum")) {
        oak_view_u64 v = { words, size };
        uint64_t t = oak_bench_sum(v); memcpy(out, &t, 8); sink += out[0];
      } else if (!strcmp(kernel, "search")) {
        oak_view_u64 k = { words, size }, p = { probes, probe_count };
        uint32_t h = oak_bench_search(k, p); memcpy(out, &h, 4); sink += h;
      } else { fprintf(stderr, "unknown kernel %s\n", kernel); return 2; }
    }
    double end = now_ns();
    ns[s] = (end - start) / rounds;
    if (sink == 0xFFFFFFFFFFFFFFFFull) fprintf(stderr, "sink\n");
  }
  size_t width = !strcmp(kernel, "sha256") || !strcmp(kernel, "blake3") ? 32 : (!strcmp(kernel, "sum") ? 8 : 4);
  for (size_t i = 0; i < width; ++i) sprintf(checksum + 2 * i, "%02x", out[i]);
  qsort(ns, samples, sizeof(double), cmp_double);
  printf("{\"impl\":\"oak\",\"kernel\":\"%s\",\"size\":%u,\"checksum\":\"%s\",\"ns_per_op_median\":%.1f,\"samples\":[", kernel, size, checksum, ns[samples / 2]);
  for (int s = 0; s < samples; ++s) printf("%s%.1f", s ? "," : "", ns[s]);
  printf("]}\n");
  return 0;
}
