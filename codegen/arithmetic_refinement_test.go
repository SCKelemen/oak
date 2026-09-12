package codegen

import (
	"strings"
	"testing"
)

// The total-arithmetic macro families are transliterated line for line in
// spec/lean/Oak/ArithmeticRefinement.lean, where each body is proved equal
// to Lean's fixed-width operator — the semantics the extraction gives the
// Oak operators. That proof is about the text below; this test pins the
// emitted text to it, so a change to either side has to visit the other
// (docs/spec/65-machine-memory.md §12 and STATUS.md name the pair).
var arithmeticMacroLines = []string{
	`#define OAK_ARITH_U(T) \`,
	`  static inline T oak_add_##T(T a, T b) { return (T)((u64)a + (u64)b); } \`,
	`  static inline T oak_sub_##T(T a, T b) { return (T)((u64)a - (u64)b); } \`,
	`  static inline T oak_neg_##T(T a) { return (T)(0u - (u64)a); } \`,
	`  static inline T oak_mul_##T(T a, T b) { return (T)((u64)a * (u64)b); } \`,
	`  static inline T oak_div_##T(T a, T b) { if (b == 0) { __builtin_trap(); } return (T)(a / b); } \`,
	`  static inline T oak_rem_##T(T a, T b) { if (b == 0) { __builtin_trap(); } return (T)(a % b); }`,
	`#define OAK_ARITH_I(T, U, MIN) \`,
	`  static inline T oak_pun_##T(U bits) { union { U from; T to; } pun; pun.from = bits; return pun.to; } \`,
	`  static inline T oak_add_##T(T a, T b) { return oak_pun_##T((U)((u64)(U)a + (u64)(U)b)); } \`,
	`  static inline T oak_sub_##T(T a, T b) { return oak_pun_##T((U)((u64)(U)a - (u64)(U)b)); } \`,
	`  static inline T oak_neg_##T(T a) { return oak_pun_##T((U)(0u - (u64)(U)a)); } \`,
	`  static inline T oak_mul_##T(T a, T b) { return oak_pun_##T((U)((u64)(U)a * (u64)(U)b)); } \`,
	`  static inline T oak_div_##T(T a, T b) { if (b == 0) { __builtin_trap(); } if (a == MIN && b == -1) { return a; } return (T)(a / b); } \`,
	`  static inline T oak_rem_##T(T a, T b) { if (b == 0) { __builtin_trap(); } if (b == -1) { return 0; } return (T)(a % b); }`,
	`OAK_ARITH_U(u8) OAK_ARITH_U(u16) OAK_ARITH_U(u32) OAK_ARITH_U(u64)`,
	`OAK_ARITH_I(i8, u8, INT8_MIN) OAK_ARITH_I(i16, u16, INT16_MIN) OAK_ARITH_I(i32, u32, INT32_MIN) OAK_ARITH_I(i64, u64, INT64_MIN)`,
}

func TestArithmeticMacrosMatchLeanTransliteration(t *testing.T) {
	output := generateC(t, "package main\n\nmain: (): i32 {\n  a: u8 = u8(200)\n  b: i64 = i64(-7)\n  i32_bits_u32(u32(a + u8(100))) + i32_trunc_i64(b * i64(3) / i64(2) % i64(5))\n}\n")
	for _, line := range arithmeticMacroLines {
		if !strings.Contains(output, line+"\n") {
			t.Fatalf("emitted prelude lacks the pinned macro line\n%s\n— update spec/lean/Oak/ArithmeticRefinement.lean with it; output:\n%s", line, output)
		}
	}
}
