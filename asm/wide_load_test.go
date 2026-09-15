package asm

import (
	"strings"
	"testing"
)

// A wide load over a byte span (docs/spec/94-assembler.md §8, wide loads):
// under the slack guard `i + 8 <= len` the checker admits `ldr x, [base,
// wI, uxtw]` as it admits a vector load, and the verifier reads it as the
// little-endian assembly of the eight bytes — the term the Oak word
// assembly spells (Oak.Assembler.wide_load_assembles) — so the fused load
// is proven equal to the eight reads; a big-endian body is refuted.
func TestVerifyWideLoadAssembles(t *testing.T) {
	decl := "word_at: (v: []u8, i: u32) -> u64"
	body := "  bind x0, w1 = v\n  bind w2 = i\n  clobber x9, x10\n  cmp w1, #8\n  b.lo trap\n  sub w9, w1, #8\n  cmp w2, w9\n  b.hi trap\n  ldr x10, [x0, w2, uxtw]\n  mov x0, x10\n  ret\ntrap:\n  brk #1"
	le := "u64(v[i]) | (u64(v[i + u32(1)]) << u64(8)) | (u64(v[i + u32(2)]) << u64(16)) | (u64(v[i + u32(3)]) << u64(24)) | (u64(v[i + u32(4)]) << u64(32)) | (u64(v[i + u32(5)]) << u64(40)) | (u64(v[i + u32(6)]) << u64(48)) | (u64(v[i + u32(7)]) << u64(56))"
	if v := verifyCase(t, decl, le, body); v.Kind != VerdictProven {
		t.Fatalf("the wide load must be proven equal to the little-endian assembly, got %s: %s", v.Kind, v.Message)
	}
	be := "u64(v[i + u32(7)]) | (u64(v[i + u32(6)]) << u64(8)) | (u64(v[i + u32(5)]) << u64(16)) | (u64(v[i + u32(4)]) << u64(24)) | (u64(v[i + u32(3)]) << u64(32)) | (u64(v[i + u32(2)]) << u64(40)) | (u64(v[i + u32(1)]) << u64(48)) | (u64(v[i]) << u64(56))"
	if v := verifyCase(t, decl, be, body); v.Kind != VerdictMismatch {
		t.Fatalf("a big-endian assembly against the load must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
	// Without the slack guard the checker refuses the wide access.
	unguarded := strings.Replace(body, "  cmp w1, #8\n  b.lo trap\n  sub w9, w1, #8\n  cmp w2, w9\n  b.hi trap\n", "  cmp w2, w1\n  b.hs trap\n", 1)
	unit, errs := ParseUnit("v.oakasm", decl+" = {\n"+unguarded+"\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	sig, err := parseSignature(decl)
	if err != nil {
		t.Fatal(err)
	}
	if findings := Check(unit.Functions[0], sig, nil); len(findings) == 0 {
		t.Fatalf("a wide load under a one-element guard must be refused")
	}
}
