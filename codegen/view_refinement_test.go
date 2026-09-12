package codegen

import (
	"strings"
	"testing"
)

// The view and span access helpers are transliterated in
// spec/lean/Oak/ViewRefinement.lean, where their guards are proved to be
// exactly the spec's bounds conditions and their reads to land inside the
// backing array. That proof is about the text below; this test pins the
// emitted helpers to it, so a change to either side has to visit the other.
var viewHelperLines = []string{
	"static inline u32 oak_view_index_u32(oak_view_u32 v, u64 i) {\n  if (i >= (u64)v.len) { __builtin_trap(); }\n  return v.base[i];\n}\n",
	"static inline oak_view_u32 oak_view_subslice_u32(oak_view_u32 v, u64 start, u64 n) {\n  if (start > (u64)v.len || n > (u64)v.len - start) { __builtin_trap(); }\n  return (oak_view_u32){ v.base + start, (u32)n };\n}\n",
	"static inline u32 oak_span_index_u32(oak_span_u32 v, u64 i) {\n  if (i >= (u64)v.len) { __builtin_trap(); }\n  return v.base[i];\n}\n",
	"static inline void oak_span_store_u32(oak_span_u32 v, u64 i, u32 value) {\n  if (i >= (u64)v.len) { __builtin_trap(); }\n  v.base[i] = value;\n}\n",
	"static inline oak_span_u32 oak_span_subslice_u32(oak_span_u32 v, u64 start, u64 n) {\n  if (start > (u64)v.len || n > (u64)v.len - start) { __builtin_trap(); }\n  return (oak_span_u32){ v.base + start, (u32)n };\n}\n",
}

func TestViewHelpersMatchLeanTransliteration(t *testing.T) {
	output := generateC(t, "package main\n\nfill: (s: [*]u32): () {\n  s[u32(0)] = u32(1)\n  rest: [*]u32 = subslice(s, u32(1), u32(2))\n  rest[u32(0)] = u32(2)\n}\n\nsum: (v: []u32): u32 {\n  head: []u32 = subslice(v, u32(0), u32(2))\n  head[u32(0)] + v[u32(1)]\n}\n\nmain: (): i32 {\n  data: [4]u32\n  fill(span(&data))\n  i32_bits_u32(sum(view(&data)))\n}\n")
	for _, helper := range viewHelperLines {
		if !strings.Contains(output, helper) {
			t.Fatalf("emitted C lacks the pinned helper\n%s\n— update spec/lean/Oak/ViewRefinement.lean with it; output:\n%s", helper, output)
		}
	}
}
