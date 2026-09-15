package asm

import (
	"strings"
	"testing"
)

// The movemask sequence the native backend emits (nativegen/simd.go
// simdMovemask): the top bit of each byte lane into bit k of w0, from the
// mask vector in v0 with v1 scratch and x9/x10 scratch.
const movemaskSequence = `  movz x9, #513
  movk x9, #2052, lsl #16
  movk x9, #8208, lsl #32
  movk x9, #32832, lsl #48
  dup v1.2d, x9
  sshr v0.16b, v0.16b, #7
  and v0.16b, v0.16b, v1.16b
  ext v1.16b, v0.16b, v0.16b, #8
  addv b0, v0.8b
  addv b1, v1.8b
  umov w9, v0.b[0]
  umov w10, v1.b[0]
  lsl w10, w10, #8
  orr w0, w9, w10
  ret`

// A vector load through a span under the checker's slack idiom, the lanes
// compared with zero, the mask returned (docs/spec/94-assembler.md §8, the
// vector increment).
func TestVerifyVectorSpanLoadMask(t *testing.T) {
	decl := "zero_mask: (b: []u8, i: u32) -> u32"
	oak := "simd.movemask_u8x16(simd.eq_u8x16(simd.load_u8x16(b, i), simd.splat_u8x16(u8(0))))"
	guarded := `  bind x0, w1 = b
  bind w2 = i
  clobber x9, x10, v0, v1
  cmp w1, #16
  b.lo trap
  sub w9, w1, #16
  cmp w2, w9
  b.hi trap
  ldr q0, [x0, w2, uxtw]
`
	proven := verifyCase(t, decl, oak, guarded+"  cmeq v0.16b, v0.16b, #0\n"+movemaskSequence+"\ntrap:\n  brk #1")
	if proven.Kind != VerdictProven {
		t.Fatalf("the zero mask must be proven, got %s: %s", proven.Kind, proven.Message)
	}
	// Comparing with one instead of zero is a definite mismatch.
	wrong := verifyCase(t, decl, oak, guarded+"  movz w9, #1\n  dup v1.16b, w9\n  cmeq v0.16b, v0.16b, v1.16b\n"+movemaskSequence+"\ntrap:\n  brk #1")
	if wrong.Kind != VerdictMismatch || !strings.Contains(wrong.Message, "disagrees") {
		t.Fatalf("comparing with one must be a mismatch, got %s: %s", wrong.Kind, wrong.Message)
	}
}

// A vector parameter and a vector result: both 64-bit halves of v0 are
// decided against the Oak lanes.
func TestVerifyVectorContract(t *testing.T) {
	decl := "double: (v: simd.U8x16) -> simd.U8x16"
	proven := verifyCase(t, decl, "simd.add_u8x16(v, v)", "  bind v0 = v\n  add v0.16b, v0.16b, v0.16b\n  ret")
	if proven.Kind != VerdictProven || !strings.Contains(proven.Message, "both halves") {
		t.Fatalf("doubling must be proven on both halves, got %s: %s", proven.Kind, proven.Message)
	}
	wrong := verifyCase(t, decl, "simd.add_u8x16(v, v)", "  bind v0 = v\n  sub v0.16b, v0.16b, v0.16b\n  ret")
	if wrong.Kind != VerdictMismatch {
		t.Fatalf("subtracting for adding must be a mismatch, got %s: %s", wrong.Kind, wrong.Message)
	}
	// A wrong lane width: adding u32 lanes where the body adds bytes
	// differs where a byte lane carries out.
	lanes := verifyCase(t, decl, "simd.add_u8x16(v, v)", "  bind v0 = v\n  add v0.4s, v0.4s, v0.4s\n  ret")
	if lanes.Kind != VerdictMismatch {
		t.Fatalf("adding at the wrong lane width must be a mismatch, got %s: %s", lanes.Kind, lanes.Message)
	}
}

// The classification shape of the UTF-8 kernel's special_cases: two
// byte-table lookups at symbolic nibble indices over symbolic tables,
// combined with and (Oak.Simd.tbl; each output bit selects among one bit
// of sixteen table lanes, so the decision stays small).
func TestVerifyVectorClassification(t *testing.T) {
	decl := "classify: (t: simd.U8x16, i: simd.U8x16, p: simd.U8x16) -> simd.U8x16"
	oak := "simd.and_u8x16(simd.tbl_u8x16(t, simd.shr_u8x16(i, u32(4))), simd.tbl_u8x16(p, simd.and_u8x16(i, simd.splat_u8x16(u8(15)))))"
	body := `  bind v0 = t
  bind v1 = i
  bind v2 = p
  clobber w9, v3
  ushr v3.16b, v1.16b, #4
  tbl v0.16b, {v0.16b}, v3.16b
  movz w9, #15
  dup v3.16b, w9
  and v3.16b, v1.16b, v3.16b
  tbl v2.16b, {v2.16b}, v3.16b
  and v0.16b, v0.16b, v2.16b
  ret`
	verdict := verifyCase(t, decl, oak, body)
	if verdict.Kind != VerdictProven {
		t.Fatalf("the classification must be proven, got %s: %s", verdict.Kind, verdict.Message)
	}
	// Indexing the low table by the high nibble too is a mismatch.
	wrong := verifyCase(t, decl, oak, strings.Replace(body, "  and v3.16b, v1.16b, v3.16b\n", "  ushr v3.16b, v1.16b, #4\n", 1))
	if wrong.Kind != VerdictMismatch {
		t.Fatalf("the wrong index must be a mismatch, got %s: %s", wrong.Kind, wrong.Message)
	}
}

// The saturating and ordering operations over symbolic vectors: ext as
// prev, umin/umax, uqsub as subs.
func TestVerifyVectorSaturation(t *testing.T) {
	decl := "saturate: (t: simd.U8x16, i: simd.U8x16, p: simd.U8x16) -> simd.U8x16"
	oak := "simd.subs_u8x16(simd.min_u8x16(simd.prev_u8x16(p, i, u32(1)), simd.max_u8x16(i, t)), i)"
	body := `  bind v0 = t
  bind v1 = i
  bind v2 = p
  clobber v4
  umax v4.16b, v1.16b, v0.16b
  ext v2.16b, v2.16b, v1.16b, #15
  umin v2.16b, v2.16b, v4.16b
  uqsub v0.16b, v2.16b, v1.16b
  ret`
	verdict := verifyCase(t, decl, oak, body)
	if verdict.Kind != VerdictProven {
		t.Fatalf("the saturation must be proven, got %s: %s", verdict.Kind, verdict.Message)
	}
	// ext by 14 is prev by 2, not 1.
	shifted := verifyCase(t, decl, oak, strings.Replace(body, "#15", "#14", 1))
	if shifted.Kind != VerdictMismatch {
		t.Fatalf("the wrong ext position must be a mismatch, got %s: %s", shifted.Kind, shifted.Message)
	}
}

// Word lanes and the any/all reductions: umaxv over the bytes of a lane
// mask is nonzero exactly when some lane is.
func TestVerifyVectorWordLanes(t *testing.T) {
	decl := "hit: (x: u32) -> u32"
	oak := "simd.any_u32x4(simd.eq_u32x4(simd.splat_u32x4(x), simd.splat_u32x4(u32(13)))) ? u32(1) | u32(0)"
	body := `  bind w0 = x
  clobber w9, v0, v1
  dup v0.4s, w0
  movz w9, #13
  dup v1.4s, w9
  cmeq v0.4s, v0.4s, v1.4s
  umaxv b0, v0.16b
  umov w9, v0.b[0]
  cmp w9, #0
  cset w0, ne
  ret`
	verdict := verifyCase(t, decl, oak, body)
	if verdict.Kind != VerdictProven {
		t.Fatalf("the word-lane hit must be proven, got %s: %s", verdict.Kind, verdict.Message)
	}
}

// A vector through the frame: a q store and load round-trip the value as
// two 8-byte slots.
func TestVerifyVectorFrameRoundTrip(t *testing.T) {
	decl := "through: (v: simd.U8x16) -> simd.U8x16"
	body := `  bind v0 = v
  clobber v1
  frame 16
  sub sp, sp, #16
  str q0, [sp]
  ldr q1, [sp]
  add sp, sp, #16
  orr v0.16b, v1.16b, v1.16b
  ret`
	verdict := verifyCase(t, decl, "v", body)
	if verdict.Kind != VerdictProven {
		t.Fatalf("the frame round trip must be proven, got %s: %s", verdict.Kind, verdict.Message)
	}
}

// The any/all reductions over free lanes: the umaxv chain compared with
// zero distributes into per-lane tests (cmpTerm, Oak.NeonSemantics
// umaxv_ne_zero_iff), where the chain's own diagram exceeded the budget.
func TestVerifyVectorAnyFreeLanes(t *testing.T) {
	decl := "anyv: (a: simd.U8x16) -> u32"
	body := "  bind v0 = a\n  clobber w10\n  umaxv b0, v0.16b\n  umov w10, v0.b[0]\n  cmp w10, #0\n  cset w0, ne\n  ret"
	verdict := verifyCase(t, decl, "simd.any_u8x16(a) ? u32(1) | u32(0)", body)
	if verdict.Kind != VerdictProven {
		t.Fatalf("any over free lanes must be proven, got %s: %s", verdict.Kind, verdict.Message)
	}
	// uminv for umaxv: some lane zero and another nonzero refutes it.
	wrong := verifyCase(t, decl, "simd.any_u8x16(a) ? u32(1) | u32(0)", strings.Replace(body, "umaxv", "uminv", 1))
	if wrong.Kind != VerdictMismatch {
		t.Fatalf("the min reduction must be a mismatch, got %s: %s", wrong.Kind, wrong.Message)
	}
}

// A vector exclusive-or of a register with itself is zero, not the move
// that `orr vD, vN, vN` is: the backend spells `xor(v, v)` so once it reads
// v in place (nativegen/simd.go vecOperand), and a model that read it as a
// move refuted the correct body (and would have proven `xor(v, v) = v`).
func TestVerifyVectorSelfXor(t *testing.T) {
	decl := "selfxor: (v: []u8) -> u32"
	oak := "{\n  x: simd.U8x16 = simd.load_u8x16(v, u32(0))\n  simd.any_u8x16(simd.xor_u8x16(x, x)) ? u32(1) | u32(0)\n}"
	asm := "  bind x0, w1 = v\n  clobber w9, w10, v16, v17\n  cmp w1, #16\n  b.lo trap\n  sub w10, w1, #16\n  cmp wzr, w10\n  b.hi trap\n  ldr q16, [x0]\n  eor v17.16b, v16.16b, v16.16b\n  umaxv b17, v17.16b\n  umov w9, v17.b[0]\n  cmp w9, #0\n  cset w0, ne\n  ret\ntrap:\n  brk #1"
	proven := verifyCase(t, decl, oak, asm)
	if proven.Kind != VerdictProven {
		t.Fatalf("xor(x, x) as eor vD, vN, vN must be proven zero, got %s: %s", proven.Kind, proven.Message)
	}
	// The move in its place is a different function: refuted with the
	// bytes named.
	moved := verifyCase(t, decl, oak, strings.Replace(asm, "eor v17.16b, v16.16b, v16.16b", "orr v17.16b, v16.16b, v16.16b", 1))
	if moved.Kind != VerdictMismatch {
		t.Fatalf("a move where the body xors must be a mismatch, got %s: %s", moved.Kind, moved.Message)
	}
}
