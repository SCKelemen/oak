/* Keep the generated C in its own translation unit; no C++ ABI assumptions. */
#define main oak_benchmark_unused_main
#include "schema.c"
#undef main
#include "bridge_event.h"
int oak_benchmark_decode(const char *data, uint32_t length, EventOutput *out) {
  oak_view_u8 src = { (const u8 *)data, length };
  oak_Result_Event_JsonDecodeError result = oak___oak_json_decode_Event(src);
  if (result.tag != oak_Result_Event_JsonDecodeError_tag_Ok) return 0;
  out->id = result.payload.Ok.id;
  out->kind_offset = (uint32_t)(result.payload.Ok.kind.base - (const u8 *)data);
  out->kind_length = result.payload.Ok.kind.len;
  out->message_offset = (uint32_t)(result.payload.Ok.message.base - (const u8 *)data);
  out->message_length = result.payload.Ok.message.len;
  for (unsigned i = 0; i < 64; ++i) out->latencies[i] = result.payload.Ok.latencies.v[i];
  for (unsigned i = 0; i < 8; ++i) out->deltas[i] = result.payload.Ok.deltas.v[i];
  return 1;
}
