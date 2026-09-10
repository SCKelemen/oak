package asm

import (
	"strings"
	"testing"
)

// Byte and halfword memory, multiplication, tst, neg, mvn
// (docs/spec/94-assembler.md §7–§8): packet-buffer kernels over []u8 and
// []u16 verify, a scale by a constant is linear, and the flags of tst are
// those of the AND.
func TestVerifyInstructionBreadth(t *testing.T) {
	// A byte checksum: the element loads zero-extend into w registers, and
	// the Oak body widens each byte before adding.
	bytes := verifyCase(t, "sum_bytes: (v: []u8) -> u32",
		"{\n  acc: u32 = u32(0)\n  i: u32 = u32(0)\n  while i < len(v) {\n    acc = acc + u32(v[i])\n    i = i + u32(1)\n  }\n  acc\n}",
		"  bind x0, w1 = v\n  clobber w9, w10, w11\n  mov w9, #0\n  mov w10, #0\nloop:\n  cmp w9, w1\n  b.hs done\n  ldrb w11, [x0, w9, uxtw #0]\n  add w10, w10, w11\n  add w9, w9, #1\n  b loop\ndone:\n  mov w0, w10\n  ret")
	if bytes.Kind != VerdictProven {
		t.Fatalf("a byte checksum must be proven, got %s: %s", bytes.Kind, bytes.Message)
	}
	// A word load over bytes reads four elements at once: outside the
	// subset, trusted (not a false proof).
	wordOverBytes := verifyCase(t, "b0: (v: []u8) -> u32", "len(v) < u32(4) ? u32(0) | u32(v[0])",
		"  bind x0, w1 = v\n  cmp w1, #4\n  b.lo short\n  ldr w0, [x0]\n  ret\nshort:\n  mov w0, #0\n  ret")
	if wordOverBytes.Kind != VerdictTrusted {
		t.Fatalf("a word load over bytes must be trusted, got %s: %s", wordOverBytes.Kind, wordOverBytes.Message)
	}
	// Halfwords: the first element or zero.
	half := verifyCase(t, "first16: (v: []u16) -> u32", "len(v) == u32(0) ? u32(0) | u32(v[0])",
		"  bind x0, w1 = v\n  cmp w1, #1\n  b.lo empty\n  ldrh w0, [x0]\n  ret\nempty:\n  mov w0, #0\n  ret")
	if half.Kind != VerdictProven {
		t.Fatalf("a halfword load must be proven, got %s: %s", half.Kind, half.Message)
	}
	// The big-endian 16-bit field at the head of a packet. (The else arm is
	// parenthesized: a bare `|` after the arm would be the arm separator's
	// bitwise-or reading — the verifier refuted the unparenthesized spelling
	// as a genuine difference.)
	be16 := verifyCase(t, "be16: (p: []u8) -> u32", "len(p) < u32(2) ? u32(0) | ((u32(p[0]) << u32(8)) | u32(p[1]))",
		"  bind x0, w1 = p\n  clobber w9, w10\n  cmp w1, #2\n  b.lo short\n  ldrb w9, [x0]\n  ldrb w10, [x0, #1]\n  lsl w9, w9, #8\n  orr w0, w9, w10\n  ret\nshort:\n  mov w0, #0\n  ret")
	if be16.Kind != VerdictProven {
		t.Fatalf("the big-endian field must be proven, got %s: %s", be16.Kind, be16.Message)
	}
	// Multiplication by a constant is linear; by a register it is the
	// shift-and-add product (proven at 32 bits within budget or evidence).
	scale := verifyCase(t, "scale: (a: u32) -> u32", "a * u32(10)", "  bind w0 = a\n  clobber w9\n  mov w9, #10\n  mul w0, w0, w9\n  ret")
	if scale.Kind != VerdictProven || !strings.Contains(scale.Message, "10*a") {
		t.Fatalf("scaling by ten must be proven linearly, got %s: %s", scale.Kind, scale.Message)
	}
	wrongScale := verifyCase(t, "scale: (a: u32) -> u32", "a * u32(10)", "  bind w0 = a\n  clobber w9\n  mov w9, #12\n  mul w0, w0, w9\n  ret")
	if wrongScale.Kind != VerdictMismatch {
		t.Fatalf("scaling by twelve must be a mismatch, got %s: %s", wrongScale.Kind, wrongScale.Message)
	}
	product := verifyCase(t, "product: (a, b: u32) -> u32", "a * b", "  bind w0 = a\n  bind w1 = b\n  mul w0, w0, w1\n  ret")
	if product.Kind != VerdictProven && product.Kind != VerdictWitnessed {
		t.Fatalf("a symbolic product must be proven or witness-checked, got %s: %s", product.Kind, product.Message)
	}
	// tst sets the flags of the AND: `ne` is a bit test.
	bit := verifyCase(t, "has_bit3: (v: u32) -> Bool", "(v & u32(8)) != u32(0)", "  bind w0 = v\n  tst w0, #8\n  cset w0, ne\n  ret")
	if bit.Kind != VerdictProven {
		t.Fatalf("tst/cset ne must be proven, got %s: %s", bit.Kind, bit.Message)
	}
	wrongBit := verifyCase(t, "has_bit3: (v: u32) -> Bool", "(v & u32(8)) != u32(0)", "  bind w0 = v\n  tst w0, #4\n  cset w0, ne\n  ret")
	if wrongBit.Kind != VerdictMismatch {
		t.Fatalf("testing the wrong mask must be a mismatch, got %s: %s", wrongBit.Kind, wrongBit.Message)
	}
	// neg and mvn.
	negate := verifyCase(t, "negate: (a: u32) -> u32", "u32(0) - a", "  bind w0 = a\n  neg w0, w0\n  ret")
	if negate.Kind != VerdictProven {
		t.Fatalf("neg must be proven, got %s: %s", negate.Kind, negate.Message)
	}
	flip := verifyCase(t, "flip: (a: u64) -> u64", "a ^ u64(0xFFFFFFFFFFFFFFFF)", "  bind x0 = a\n  mvn x0, x0\n  ret")
	if flip.Kind != VerdictProven {
		t.Fatalf("mvn must be proven, got %s: %s", flip.Kind, flip.Message)
	}
	// Oak's >> is the logical shift at every type (the backend's oak_shr_u
	// helpers), so asr does not implement it: a mismatch at a negative input.
	arith := verifyCase(t, "half: (a: i32) -> i32", "a >> i32(1)", "  bind w0 = a\n  asr w0, w0, #1\n  ret")
	if arith.Kind != VerdictMismatch {
		t.Fatalf("asr for Oak's logical >> must be a mismatch, got %s: %s", arith.Kind, arith.Message)
	}
	// The checker: a strb through a read-only view is refused; the byte
	// indexed form emits without a shift amount.
	if findings := checkBody(t, "z: (v: []u8) -> u32", "  bind x0, w1 = v\n  clobber w9\n  cmp w1, #1\n  b.lo short\n  mov w9, #0\n  strb w9, [x0]\n  mov w0, #0\n  ret\nshort:\n  mov w0, #0\n  ret"); len(findings) == 0 || !strings.Contains(strings.Join(findings, "\n"), "read-only view") {
		t.Fatalf("strb through a view must be refused, got %v", findings)
	}
	unit, errs := ParseUnit("b.oakasm", "f: (v: []u8) -> u32 = {\n  bind x0, w1 = v\n  clobber w9\n  mov w9, #0\n  cmp w9, w1\n  b.hs done\n  ldrb w0, [x0, w9, uxtw #0]\n  ret\ndone:\n  mov w0, #0\n  ret\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	if text := renderOperand(unit.Functions[0].Items[3].(Instruction).Operands[1], nil, nil, nil); text != "[x0, w9, uxtw]" {
		t.Fatalf("the byte indexed form renders as %q", text)
	}
}
