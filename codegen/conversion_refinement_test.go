package codegen

import (
	"strings"
	"testing"
)

// The explicit integer conversion helpers are transliterated in
// spec/lean/Oak/ConversionRefinement.lean, where each is proved to meet
// docs/spec/20-types.md §11.1: trunc wraps, saturating clamps, bits keeps
// the pattern (checked is pinned by compiler/e2e_conversion_refinement_test.go,
// which has the Result type in scope). That proof is about the text below;
// this test pins the emitted helpers to it.
func TestConversionHelpersMatchLeanTransliteration(t *testing.T) {
	output := generateC(t, "package main\n\nmain: (): i32 {\n  a: u8 = u8_trunc_u32(u32(300))\n  b: i8 = i8_trunc_i32(i32(200))\n  c: u8 = u8_saturating_u32(u32(300))\n  d: i8 = i8_saturating_i32(i32(-200))\n  e: i32 = i32_bits_u32(u32(4294967295))\n  f: u32 = u32_bits_i32(i32(-1))\n  i32(a) + i32(b) + i32(c) + i32(d) + e + i32_bits_u32(f)\n}\n")
	for _, helper := range []string{
		"static inline u8 oak_conv_u8_trunc_u32( u32 x ) {\n  return (u8)( x );\n}\n",
		"static inline i8 oak_conv_i8_trunc_i32( i32 x ) {\n  union { u8 low; i8 to; } pun;\n  pun.low = (u8)( (u32)x );\n  return pun.to;\n}\n",
		"static inline u8 oak_conv_u8_saturating_u32( u32 x ) {\n  return x > (u32)255u ? (u8)255u : (u8)x;\n}\n",
		"static inline i8 oak_conv_i8_saturating_i32( i32 x ) {\n  if (x > (i32)127) { return (i8)127; }\n  if (x < (i32)(-128)) { return (i8)(-128); }\n  return (i8)x;\n}\n",
		"static inline i32 oak_conv_i32_bits_u32( u32 x ) {\n  union { u32 from; i32 to; } pun;\n  pun.from = x;\n  return pun.to;\n}\n",
		"static inline u32 oak_conv_u32_bits_i32( i32 x ) {\n  union { i32 from; u32 to; } pun;\n  pun.from = x;\n  return pun.to;\n}\n",
	} {
		if !strings.Contains(output, helper) {
			t.Fatalf("emitted C lacks the pinned helper\n%s\n— update spec/lean/Oak/ConversionRefinement.lean with it; output:\n%s", helper, output)
		}
	}
}
