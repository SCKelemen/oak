#ifndef OAK_JSON_BENCH_BRIDGE_H
#define OAK_JSON_BENCH_BRIDGE_H
#include <stdint.h>
typedef struct {
  uint64_t id;
  uint32_t active;
  int32_t samples[4];
} BenchOutput;
#ifdef __cplusplus
extern "C" {
#endif
int oak_benchmark_decode(const char *data, uint32_t length, BenchOutput *out);
#ifdef __cplusplus
}
#endif
#endif
