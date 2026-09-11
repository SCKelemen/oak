/* Shared harness pieces for the standard-library benchmarks: the workload
   table a bridge exports, deterministic corpus generation, checksums; the
   timer lives in runner.c. Every generator here has a byte-identical twin in
   goref/corpus.go; the driver refuses to time a workload whose Oak and Go
   preflight checksums disagree. */
#ifndef OAK_STDLIB_BENCH_RUNNER_H
#define OAK_STDLIB_BENCH_RUNNER_H
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* A workload is one measured operation over one corpus. `setup` builds the
   corpus for the given scale (1.0 is the documented size); `run` performs
   the operation with the named backend and returns the checksum the runner
   compares with the preflight value; `teardown` releases the corpus so the
   sanitizer build (LeakSanitizer on Linux) exits clean and a leak inside
   generated Oak code stays visible. `items` and `bytes` describe one run. */
typedef struct {
  const char *name;            /* "package/operation" */
  const char *backends[3];     /* "oak" first, then optional C references */
  int backend_count;
  void (*setup)(double scale);
  uint64_t (*run)(int backend);
  void (*teardown)(void);      /* frees what setup allocated */
  uint64_t items;
  uint64_t bytes;
} BenchWorkload;

/* Each bridge defines these. */
extern BenchWorkload bench_workloads[];
extern const int bench_workload_count;

/* SplitMix64, the corpus generator shared with goref/corpus.go. */
static inline uint64_t bench_next(uint64_t *state) {
  uint64_t z = (*state += UINT64_C(0x9e3779b97f4a7c15));
  z = (z ^ (z >> 30)) * UINT64_C(0xbf58476d1ce4e5b9);
  z = (z ^ (z >> 27)) * UINT64_C(0x94d049bb133111eb);
  return z ^ (z >> 31);
}

static inline uint64_t bench_fnv_bytes(const uint8_t *data, size_t length) {
  uint64_t acc = UINT64_C(14695981039346656037);
  for (size_t i = 0; i < length; ++i) acc = (acc ^ data[i]) * UINT64_C(1099511628211);
  return acc;
}

static inline uint64_t bench_fnv_u64(const uint64_t *values, size_t count) {
  uint64_t acc = UINT64_C(14695981039346656037);
  for (size_t i = 0; i < count; ++i) acc = (acc ^ values[i]) * UINT64_C(1099511628211);
  return acc;
}

static inline uint64_t bench_fnv_u32(const uint32_t *values, size_t count) {
  uint64_t acc = UINT64_C(14695981039346656037);
  for (size_t i = 0; i < count; ++i) acc = (acc ^ (uint64_t)values[i]) * UINT64_C(1099511628211);
  return acc;
}

static inline void *bench_alloc(size_t bytes) {
  void *memory = malloc(bytes ? bytes : 1);
  if (!memory) { fprintf(stderr, "allocation of %zu bytes failed\n", bytes); exit(1); }
  return memory;
}

static inline size_t bench_scaled(double scale, size_t base) {
  double scaled = (double)base * scale;
  if (scaled < 1) return 1;
  return (size_t)scaled;
}

/* Corpus generators; the Go twins live in goref/corpus.go. */

static inline void bench_fill_bytes(uint8_t *dst, size_t count, uint64_t seed) {
  uint64_t state = seed, word = 0;
  for (size_t i = 0; i < count; ++i) {
    if (i % 8 == 0) word = bench_next(&state);
    dst[i] = (uint8_t)(word >> ((i % 8) * 8));
  }
}

static inline void bench_fill_u32(uint32_t *dst, size_t count, uint64_t seed) {
  uint64_t state = seed;
  for (size_t i = 0; i < count; ++i) dst[i] = (uint32_t)bench_next(&state);
}

/* Varint corpus: a length 1..10 bytes chosen uniformly, then a value that
   needs at most that many LEB128 bytes (exactly ten when the length is ten). */
static inline void bench_fill_varints(uint64_t *dst, size_t count, uint64_t seed) {
  uint64_t state = seed;
  for (size_t i = 0; i < count; ++i) {
    uint64_t r = bench_next(&state);
    unsigned k = 1 + (unsigned)(r % 10);
    uint64_t v = bench_next(&state);
    if (k == 10) v |= UINT64_C(1) << 63;
    else v >>= 64 - 7 * k;
    dst[i] = v;
  }
}

static const char bench_unreserved[] = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-._~";
static const char bench_reserved[] = "!*'();:@&=+$,/?#[]%{}|^<>\"`\\";

/* Percent-encoding corpus: 70% unreserved, 30% reserved or high bytes; no
   spaces, so Oak's percent_encode and Go's url.QueryEscape agree. */
static inline void bench_fill_percent(uint8_t *dst, size_t count, uint64_t seed) {
  uint64_t state = seed;
  for (size_t i = 0; i < count; ++i) {
    uint64_t r = bench_next(&state);
    if (r % 10 < 7) dst[i] = (uint8_t)bench_unreserved[(r >> 8) % (sizeof bench_unreserved - 1)];
    else if ((r >> 4) % 4 == 0) dst[i] = (uint8_t)(0x80 + (r >> 16) % 128);
    else dst[i] = (uint8_t)bench_reserved[(r >> 16) % (sizeof bench_reserved - 1)];
  }
}

/* UTF-8 corpus: 60% ASCII, 25% two-byte, 10% three-byte, 5% four-byte
   scalars, whole scalars only, at most `capacity` bytes. Returns the length. */
static inline size_t bench_fill_utf8(uint8_t *dst, size_t capacity, uint64_t seed) {
  uint64_t state = seed;
  size_t at = 0;
  for (;;) {
    uint64_t r = bench_next(&state);
    uint64_t c = r % 100, bits = r >> 8;
    uint32_t s;
    if (c < 60) s = (uint32_t)(bits % 128);
    else if (c < 85) s = (uint32_t)(0x80 + bits % (0x800 - 0x80));
    else if (c < 95) { s = (uint32_t)(0x800 + bits % (0x10000 - 0x800)); if (s >= 0xD800 && s <= 0xDFFF) s -= 0x800; }
    else s = (uint32_t)(0x10000 + bits % (0x110000 - 0x10000));
    size_t width = s < 0x80 ? 1 : s < 0x800 ? 2 : s < 0x10000 ? 3 : 4;
    if (at + width > capacity) return at;
    if (width == 1) dst[at] = (uint8_t)s;
    else if (width == 2) { dst[at] = (uint8_t)(0xC0 | (s >> 6)); dst[at + 1] = (uint8_t)(0x80 | (s & 0x3F)); }
    else if (width == 3) { dst[at] = (uint8_t)(0xE0 | (s >> 12)); dst[at + 1] = (uint8_t)(0x80 | ((s >> 6) & 0x3F)); dst[at + 2] = (uint8_t)(0x80 | (s & 0x3F)); }
    else { dst[at] = (uint8_t)(0xF0 | (s >> 18)); dst[at + 1] = (uint8_t)(0x80 | ((s >> 12) & 0x3F)); dst[at + 2] = (uint8_t)(0x80 | ((s >> 6) & 0x3F)); dst[at + 3] = (uint8_t)(0x80 | (s & 0x3F)); }
    at += width;
  }
}

/* Decimal corpus: values with 1..20 digits, uniform in length. */
static inline void bench_fill_decimals(uint64_t *dst, size_t count, uint64_t seed) {
  uint64_t state = seed;
  for (size_t i = 0; i < count; ++i) {
    uint64_t r = bench_next(&state);
    unsigned k = 1 + (unsigned)(r % 20);
    uint64_t v = bench_next(&state);
    if (k < 20) {
      uint64_t limit = 1;
      for (unsigned j = 0; j < k; ++j) limit *= 10;
      v %= limit;
    }
    dst[i] = v;
  }
}

/* Writes the decimal text of `values`, one per line; returns the length. */
static inline size_t bench_write_decimals(uint8_t *dst, const uint64_t *values, size_t count) {
  size_t at = 0;
  for (size_t i = 0; i < count; ++i) {
    char digits[24];
    int n = snprintf(digits, sizeof digits, "%llu\n", (unsigned long long)values[i]);
    memcpy(dst + at, digits, (size_t)n);
    at += (size_t)n;
  }
  return at;
}

/* Instants: nanoseconds uniform in about ±2^61 around the epoch, never 0. */
static inline void bench_fill_instants(int64_t *dst, size_t count, uint64_t seed) {
  uint64_t state = seed;
  for (size_t i = 0; i < count; ++i) {
    int64_t nanos = (int64_t)(bench_next(&state) >> 2) - (INT64_C(1) << 61);
    dst[i] = nanos == 0 ? 1 : nanos;
  }
}

#endif
