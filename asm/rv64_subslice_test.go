package asm

import (
	"strings"
	"testing"
)

// The derived-span idiom on the rv64 lane (docs/spec/94-assembler.md §9,
// subslice): `bltu norm, start, trap` proves start <= len, `sub rest,
// norm, start` forms len - start, `bltu rest, n, trap` proves n <= len -
// start, and `add base', base, start << s` derives the span whose length
// register is n — so a guarded element access through the derived base is
// admitted. Without the count guard the derivation does not happen and the
// access is refused.
func TestRV64CheckSubslice(t *testing.T) {
	// second: (v: []u16, start: u32, n: u32) -> u16 { w: []u16 = subslice(v, start, n); w[1] }
	body := "  bind a0, a1 = v\n  bind a2 = start\n  bind a3 = n\n  clobber t0, t1, t2, t3, a4\n  frame 96\n  addi sp, sp, -96\n  sd s1, 0(sp)\n  sd s2, 8(sp)\n  slli a4, a1, 32\n  srli a4, a4, 32\n  mv t0, a2\n  slli t0, t0, 32\n  srli t0, t0, 32\n  mv t1, a3\n  slli t1, t1, 32\n  srli t1, t1, 32\n  mv s2, t1\n  bltu a4, t0, trap\n  sub t2, a4, t0\n  bltu t2, s2, trap\n  slli t3, t0, 1\n  add s1, a0, t3\n  li t0, 1\n  bgeu t0, s2, trap\n  slli t0, t0, 1\n  add t0, s1, t0\n  lhu a0, 0(t0)\n  ld s1, 0(sp)\n  ld s2, 8(sp)\n  addi sp, sp, 96\n  ret\ntrap:\n  ebreak"
	decl := "second: (v: []u16, start: u32, n: u32) -> u16"
	fn, errs := rv64Unit(t, decl, body)
	if len(errs) != 0 {
		t.Fatalf("parse: %v", errs)
	}
	sig, err := parseSignature(decl)
	if err != nil {
		t.Fatal(err)
	}
	if findings := Check(fn, sig, nil); len(findings) != 0 {
		t.Fatalf("the derived-span idiom must be admitted: %v", findings)
	}
	// Without the count guard, n is not bounded by len - start: no span is
	// derived and the element access through s1 is refused.
	unguarded := strings.Replace(body, "  sub t2, a4, t0\n  bltu t2, s2, trap\n", "", 1)
	fn, errs = rv64Unit(t, decl, unguarded)
	if len(errs) != 0 {
		t.Fatalf("parse: %v", errs)
	}
	findings := Check(fn, sig, nil)
	if len(findings) == 0 {
		t.Fatalf("a subslice without the count guard must be refused")
	}
	if !strings.Contains(findings[0], "memory through") {
		t.Fatalf("unexpected finding: %v", findings)
	}
}
