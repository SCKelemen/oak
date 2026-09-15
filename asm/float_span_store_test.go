package asm

import "testing"

// A scalar float store through a span in a loop body (docs/spec/94-assembler.md
// §8): `str sN, [xB, wI, uxtw #2]` writes the register's low lane at the
// element's width into the span's write log, so `v[i] = v[i] * k` over a
// `[*]f32` is proven up to the IEEE operations, and the wrong operation is
// refuted. Before this the s view's store was trusted while d's proved.
func TestVerifyFloatSpanStoreLoop(t *testing.T) {
	decl := "scale: (v: [*]f32, k: f32) -> u32"
	body := `  bind x0, w1 = v
  bind s0 = k
  clobber x9, x19, x20, d16, d17, d8, x2
  frame 144
  sub sp, sp, #144
  stp x19, x20, [sp]
  str d8, [sp, #80]
  mov x19, x0
  mov w20, w1
  fmov s8, s0
  mov w2, wzr
loop_4:
  cmp w2, w20
  b.hs done_5
  ldr s17, [x19, w2, uxtw #2]
  fmul s16, s17, s8
  str s16, [x19, w2, uxtw #2]
  add w2, w2, #1
  b loop_4
done_5:
  mov w0, w2
ret_2:
  ldr d8, [sp, #80]
  ldp x19, x20, [sp]
  add sp, sp, #144
  ret`
	oak := func(update string) string {
		return "{\n  i: u32 = u32(0)\n  while i < len(v) {\n    v[i] = " + update + "\n    i = i + u32(1)\n  }\n  i\n}"
	}
	if v := verifyCase(t, decl, oak("v[i] * k"), body); v.Kind != VerdictProven {
		t.Fatalf("the float span store loop must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := verifyCase(t, decl, oak("v[i] + k"), body); v.Kind != VerdictMismatch {
		t.Fatalf("a sum against fmul must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
}
