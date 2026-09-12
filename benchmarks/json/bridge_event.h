#ifndef OAK_JSON_BENCH_BRIDGE_EVENT_H
#define OAK_JSON_BENCH_BRIDGE_EVENT_H
#include <stdint.h>
/* Borrowed string fields come back as offsets into the input and lengths,
   quotes included: both decoders hand out the raw token, neither copies. */
typedef struct {
  uint64_t id;
  uint32_t kind_offset, kind_length;
  uint32_t message_offset, message_length;
  uint32_t latencies[64];
  int32_t deltas[8];
} EventOutput;
#ifdef __cplusplus
extern "C" {
#endif
int oak_benchmark_decode(const char *data, uint32_t length, EventOutput *out);
#ifdef __cplusplus
}
#endif
#endif
