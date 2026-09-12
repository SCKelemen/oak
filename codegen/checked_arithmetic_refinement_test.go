package codegen

import (
	"strings"
	"testing"
)

// The checked, saturating and trapping helpers and the checked shifts are
// transliterated in spec/lean/Oak/CheckedArithmeticRefinement.lean, where
// each is proved to meet docs/spec/20-types.md §11.1a over the overflow
// builtins' contract — in particular that every saturating side test picks
// the bound the exact result left. That proof is about the text below; this
// test pins the emitted helpers to it, so a change to either side has to
// visit the other.
func TestCheckedArithmeticHelpersMatchLeanTransliteration(t *testing.T) {
	output := generateC(t, "package main\n\nmain: (): i32 {\n  a: u32 = u32_saturating_add(u32(4000000000), u32(500000000))\n  b: i32 = i32_saturating_mul(i32(-70000), i32(70000))\n  c: i8 = i8_saturating_sub(i8(-100), i8(100))\n  e: u16 = u16_saturating_sub(u16(1), u16(2))\n  d: i64 = i64_trapping_sub(i64(5), i64(3))\n  s: u8 = u8(3) << u8(2)\n  i32_bits_u32(a - u32(4294967295)) + b + i32(c) + i32_trunc_i64(d) + i32(e) + i32(s)\n}\n")
	for _, helper := range []string{
		"static inline u32 oak_arith_u32_saturating_add( u32 a, u32 b ) {\n  u32 r;\n  if (__builtin_add_overflow(a, b, &r)) {\n    return (1) ? (u32)4294967295u : (u32)0u;\n  }\n  return r;\n}\n",
		"static inline i32 oak_arith_i32_saturating_mul( i32 a, i32 b ) {\n  i32 r;\n  if (__builtin_mul_overflow(a, b, &r)) {\n    return ((a < 0) == (b < 0)) ? (i32)2147483647 : (i32)(-2147483647 - 1);\n  }\n  return r;\n}\n",
		"static inline i8 oak_arith_i8_saturating_sub( i8 a, i8 b ) {\n  i8 r;\n  if (__builtin_sub_overflow(a, b, &r)) {\n    return (b < 0) ? (i8)127 : (i8)(-127 - 1);\n  }\n  return r;\n}\n",
		"static inline u16 oak_arith_u16_saturating_sub( u16 a, u16 b ) {\n  u16 r;\n  if (__builtin_sub_overflow(a, b, &r)) {\n    return (0) ? (u16)65535u : (u16)0u;\n  }\n  return r;\n}\n",
		"static inline i64 oak_arith_i64_trapping_sub( i64 a, i64 b, const char *file, u32 line ) {\n  i64 r;\n  if (__builtin_sub_overflow(a, b, &r)) { oak_overflow_trap(file, line); }\n  return r;\n}\n",
		"#define OAK_SHIFT_HELPERS(T, W) \\\n  static inline T oak_shl_##T(T v, T n) { if (n >= W) { __builtin_trap(); } return (T)(v << n); } \\\n  static inline T oak_shr_##T(T v, T n) { if (n >= W) { __builtin_trap(); } return (T)(v >> n); }\nOAK_SHIFT_HELPERS(u8, 8u) OAK_SHIFT_HELPERS(u16, 16u) OAK_SHIFT_HELPERS(u32, 32u) OAK_SHIFT_HELPERS(u64, 64u)\n",
	} {
		if !strings.Contains(output, helper) {
			t.Fatalf("emitted C lacks the pinned helper\n%s\n— update spec/lean/Oak/CheckedArithmeticRefinement.lean with it; output:\n%s", helper, output)
		}
	}
}
