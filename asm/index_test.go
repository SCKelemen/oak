package asm

import (
	"strings"
	"testing"
)

// Register-offset span addressing (docs/spec/94-assembler.md §7): a load
// `[base, wI, uxtw #s]` walks a span by element index and is admitted only
// under a dominating index guard — `cmp wI, wL; b.hs exit` (index below the
// length) or `cmp wI, #K; b.hs exit` with `len >= K` established.
func TestIndexedSpanAccess(t *testing.T) {
	decl := "sum: (v: []u32) -> u32"
	// The data-dependent walk: while i < len(v).
	walk := "  bind x0, w1 = v\n  clobber w9, w10, w11\n  mov w9, #0\n  mov w10, #0\nloop:\n  cmp w9, w1\n  b.hs done\n  ldr w11, [x0, w9, uxtw #2]\n  add w10, w10, w11\n  add w9, w9, #1\n  b loop\ndone:\n  mov w0, w10\n  ret"
	unit, errs := ParseUnit("i.oakasm", decl+" = {\n"+walk+"\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	sig, err := parseSignature(decl)
	if err != nil {
		t.Fatal(err)
	}
	if findings := Check(unit.Functions[0], sig, nil); len(findings) != 0 {
		t.Fatalf("the guarded walk must be accepted: %v", findings)
	}
	// Emission spells the operand back exactly.
	if text := renderOperand(unit.Functions[0].Items[5].(Instruction).Operands[1], nil, nil, nil); text != "[x0, w9, uxtw #2]" {
		t.Fatalf("indexed operand renders as %q", text)
	}

	rejections := []struct{ name, body, want string }{
		{"no index guard", "  bind x0, w1 = v\n  clobber w9\n  mov w9, #0\n  ldr w0, [x0, w9, uxtw #2]\n  ret", "without a dominating index guard"},
		{"guard against another register", "  bind x0, w1 = v\n  bind x2, w3 = w\n  clobber w9\n  mov w9, #0\n  cmp w9, w3\n  b.hs done\n  ldr w0, [x0, w9, uxtw #2]\n  ret\ndone:\n  mov w0, #0\n  ret", "not this span's length register"},
		{"index written after guard", "  bind x0, w1 = v\n  clobber w9\n  mov w9, #0\n  cmp w9, w1\n  b.hs done\n  add w9, w9, #1\n  ldr w0, [x0, w9, uxtw #2]\n  ret\ndone:\n  mov w0, #0\n  ret", "without a dominating index guard"},
		{"guard lost at merge", "  bind x0, w1 = v\n  clobber w9\n  mov w9, #0\n  cmp w9, w1\n  b.hs again\nagain:\n  ldr w0, [x0, w9, uxtw #2]\n  ret", "without a dominating index guard"},
		{"wrong scale", "  bind x0, w1 = v\n  clobber w9\n  mov w9, #0\n  cmp w9, w1\n  b.hs done\n  ldr w0, [x0, w9, uxtw #1]\n  ret\ndone:\n  mov w0, #0\n  ret", "whole elements"},
		{"wrong width", "  bind x0, w1 = v\n  clobber w9, x10\n  mov w9, #0\n  cmp w9, w1\n  b.hs done\n  ldr x10, [x0, w9, uxtw #3]\n  mov w0, w10\n  ret\ndone:\n  mov w0, #0\n  ret", "whole elements"},
		{"constant bound above proven length", "  bind x0, w1 = v\n  clobber w9\n  cmp w1, #2\n  b.lo short\n  mov w9, #0\n  cmp w9, #4\n  b.hs short\n  ldr w0, [x0, w9, uxtw #2]\n  ret\nshort:\n  mov w0, #0\n  ret", "proven minimum length is 2"},
		{"wrong branch sense", "  bind x0, w1 = v\n  clobber w9\n  mov w9, #0\n  cmp w9, w1\n  b.lo body\n  b fail\nbody:\n  ldr w0, [x0, w9, uxtw #2]\n  ret\nfail:\n  mov w0, #0\n  ret", "without a dominating index guard"},
		{"store through view", "  bind x0, w1 = v\n  clobber w9\n  mov w9, #0\n  cmp w9, w1\n  b.hs done\n  str w9, [x0, w9, uxtw #2]\n  mov w0, #0\n  ret\ndone:\n  mov w0, #0\n  ret", "read-only view"},
		{"indexed frame access", "  bind x0, w1 = v\n  clobber w9\n  frame 16\n  mov w9, #0\n  ldr w0, [sp, w9, uxtw #2]\n  ret", "walks a span, not the frame"},
	}
	for _, tc := range rejections {
		t.Run(tc.name, func(t *testing.T) {
			d := decl
			if strings.Contains(tc.body, "= w") {
				d = "sum: (v: []u32, w: []u32) -> u32"
			}
			unit, errs := ParseUnit("i.oakasm", d+" = {\n"+tc.body+"\n}\n")
			if len(errs) != 0 {
				t.Fatal(errs)
			}
			sig, err := parseSignature(d)
			if err != nil {
				t.Fatal(err)
			}
			findings := Check(unit.Functions[0], sig, nil)
			for _, finding := range findings {
				if strings.Contains(finding, tc.want) {
					return
				}
			}
			t.Fatalf("expected a finding mentioning %q, got: %v", tc.want, findings)
		})
	}

	// The constant-bound form: `cmp w9, #4; b.hs` under `len >= 4`.
	constBound := "  bind x0, w1 = v\n  clobber w9\n  cmp w1, #4\n  b.lo short\n  mov w9, #3\n  cmp w9, #4\n  b.hs short\n  ldr w0, [x0, w9, uxtw #2]\n  ret\nshort:\n  mov w0, #0\n  ret"
	unit, errs = ParseUnit("i.oakasm", decl+" = {\n"+constBound+"\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	if findings := Check(unit.Functions[0], sig, nil); len(findings) != 0 {
		t.Fatalf("the constant-bound form must be accepted: %v", findings)
	}
}

// The verifier resolves an indexed load along an unrolled counted loop —
// the index register is a constant on every iteration — and stays
// trusted for a data-dependent walk.
func TestVerifyIndexedLoads(t *testing.T) {
	decl := "sum4: (v: []u32) -> u32"
	// The length guard must be re-established inside the loop (guards die
	// at labels), so each iteration forks on len(v) < 4; the Oak side
	// checks once. Same function: len(v) never changes.
	loop := "  bind x0, w1 = v\n  clobber w9, w10, w11\n  mov w9, #0\n  mov w10, #0\nloop:\n  cmp w9, #4\n  b.hs done\n  cmp w1, #4\n  b.lo short\n  ldr w11, [x0, w9, uxtw #2]\n  add w10, w10, w11\n  add w9, w9, #1\n  b loop\ndone:\n  mov w0, w10\n  ret\nshort:\n  mov w0, #0\n  ret"
	oakLoop := "{\n  len(v) < u32(4) ? { u32(0) } | {\n    acc: u32 = u32(0)\n    i: u32 = u32(0)\n    while i < u32(4) {\n      acc = acc + v[i]\n      i = i + u32(1)\n    }\n    acc\n  }\n}"
	proven := verifyCase(t, decl, oakLoop, loop)
	if proven.Kind != VerdictProven {
		t.Fatalf("an indexed sum loop must be proven, got %s: %s", proven.Kind, proven.Message)
	}
	// The unrolled Oak spelling is the same function.
	flat := verifyCase(t, decl, "len(v) < u32(4) ? u32(0) | v[0] + v[1] + v[2] + v[3]", loop)
	if flat.Kind != VerdictProven {
		t.Fatalf("the flat spelling must be proven, got %s: %s", flat.Kind, flat.Message)
	}
	// Three iterations for four is a mismatch naming the missing element.
	loop3 := strings.Replace(loop, "cmp w9, #4", "cmp w9, #3", 1)
	short := verifyCase(t, decl, oakLoop, loop3)
	if short.Kind != VerdictMismatch || !strings.Contains(short.Message, "v[3]=") {
		t.Fatalf("a short loop must be a mismatch naming v[3], got %s: %s", short.Kind, short.Message)
	}
	// The data-dependent walk (while i < len(v)) is checked but trusted.
	walk := "  bind x0, w1 = v\n  clobber w9, w10, w11\n  mov w9, #0\n  mov w10, #0\nloop:\n  cmp w9, w1\n  b.hs done\n  ldr w11, [x0, w9, uxtw #2]\n  add w10, w10, w11\n  add w9, w9, #1\n  b loop\ndone:\n  mov w0, w10\n  ret"
	trusted := verifyCase(t, "sum: (v: []u32) -> u32", "u32(0)", walk)
	if trusted.Kind != VerdictTrusted {
		t.Fatalf("a data-dependent walk must be trusted, got %s: %s", trusted.Kind, trusted.Message)
	}
}
