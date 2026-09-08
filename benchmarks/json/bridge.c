/* Keep the generated C in its own translation unit; no C++ ABI assumptions. */
#define main oak_benchmark_unused_main
#include "schema.c"
#undef main
#include "bridge.h"
int oak_benchmark_decode(const char *data, uint32_t length, BenchOutput *out) {
  oak_view_u8 src = { (const u8 *)data, length };
  oak_Result_BenchRecord_JsonDecodeError result = oak_benchmark_read(src);
  if (result.tag != oak_Result_BenchRecord_JsonDecodeError_tag_Ok) return 0;
  out->id = result.payload.Ok.id;
  out->active = result.payload.Ok.active == oak_Bool_True;
  for (unsigned i = 0; i < 4; ++i) out->samples[i] = result.payload.Ok.samples[i];
  return 1;
}
