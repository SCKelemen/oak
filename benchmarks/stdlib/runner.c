/* Generic runner: `bench_<package> <scale> <samples> [workload-prefix]`.
   For every workload the bridge exports it builds the corpus, runs each
   backend once for the preflight checksum, then takes `samples` timed runs
   per backend in alternating order and prints one JSON line per run. A
   timed run whose checksum differs from the preflight is an error. */
#define _POSIX_C_SOURCE 200809L
#include <time.h>
#include "runner.h"

static uint64_t bench_now_ns(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (uint64_t)ts.tv_sec * UINT64_C(1000000000) + (uint64_t)ts.tv_nsec;
}

static void fail(const char *message) {
  fprintf(stderr, "%s\n", message);
  exit(1);
}

int main(int argc, char **argv) {
  if (argc < 3 || argc > 4) fail("usage: runner <scale> <samples> [workload-prefix]");
  double scale = atof(argv[1]);
  long samples = atol(argv[2]);
  const char *prefix = argc == 4 ? argv[3] : "";
  if (!(scale > 0 && scale <= 16) || samples < 1 || samples > 100) fail("scale must be in (0, 16], samples in 1..100");
  for (int w = 0; w < bench_workload_count; ++w) {
    BenchWorkload *work = &bench_workloads[w];
    if (strncmp(work->name, prefix, strlen(prefix)) != 0) continue;
    work->setup(scale);
    uint64_t expected = 0;
    for (int b = 0; b < work->backend_count; ++b) {
      uint64_t checksum = work->run(b);
      if (b == 0) expected = checksum;
      else if (checksum != expected) fail("preflight checksum mismatch between backends");
    }
    printf("{\"event\":\"preflight\",\"workload\":\"%s\",\"items\":%llu,\"bytes\":%llu,\"checksum\":%llu}\n",
      work->name, (unsigned long long)work->items, (unsigned long long)work->bytes, (unsigned long long)expected);
    fflush(stdout);
    for (long sample = 0; sample < samples; ++sample) {
      for (int step = 0; step < work->backend_count; ++step) {
        /* Alternate the backend order between samples to spread thermal and
           frequency drift over every backend. */
        int b = sample % 2 == 0 ? step : work->backend_count - 1 - step;
        uint64_t start = bench_now_ns();
        uint64_t checksum = work->run(b);
        uint64_t ns = bench_now_ns() - start;
        if (checksum != expected) fail("timed checksum mismatch");
        printf("{\"event\":\"sample\",\"workload\":\"%s\",\"backend\":\"%s\",\"sample\":%ld,\"ns\":%llu,\"items\":%llu,\"bytes\":%llu,\"checksum\":%llu}\n",
          work->name, work->backends[b], sample, (unsigned long long)ns,
          (unsigned long long)work->items, (unsigned long long)work->bytes, (unsigned long long)checksum);
        fflush(stdout);
      }
    }
    work->teardown();
  }
  return 0;
}
