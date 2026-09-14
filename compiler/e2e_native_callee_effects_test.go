package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// A callee's memory effects flow through the call summary
// (docs/spec/94-assembler.md §9, twenty-ninth increment): a caller passing
// its span and its by-reference record on to a unit callee is proven in
// the memory the callee writes, a loop whose count is a constant argument
// unrolls inside the summary, a read-modify-write of a word under a shift
// count bounded below the width is proven, and a caller of a callee with
// a data-dependent loop stays trusted. The C backend is the oracle for the
// values.
const nativeCalleeEffectsProgram = `
Arena: type = struct { base: u32, count_at: u32, a: u64, b: u64, c: u64 }

count: (ar: Arena, w: [*]u32) -> u32 = w[ar.count_at]
set_count: (ar: Arena, w: [*]u32, n: u32) -> () { w[ar.count_at] = n }

push_byte: (ar: Arena, w: [*]u32, b: u32) -> () {
  at: u32 = count(ar, w)
  shift: u32 = (at % u32(4)) * u32(8)
  word: u32 = ar.base + at / u32(4)
  w[word] = (w[word] & (u32(4294967295) ^ (u32(255) << shift))) | (b << shift)
  set_count(ar, w, at + u32(1))
}

push_lits: (ar: Arena, w: [*]u32, lo: u64, n: u32) -> () {
  k: u32 = u32(0)
  while k < n {
    push_byte(ar, w, u32_trunc_u64((lo >> u64(k * u32(8))) & u64(255)))
    k = k + u32(1)
  }
}

push_ab: (ar: Arena, w: [*]u32) -> () {
  push_lits(ar, w, u64(0x6261), u32(2))
}

push_then_count: (ar: Arena, w: [*]u32) -> u32 {
  push_lits(ar, w, u64(0x41), u32(1))
  count(ar, w)
}

push_n: (ar: Arena, w: [*]u32, n: u32) -> () {
  push_lits(ar, w, u64(0x7A7A), n)
}

main: (): i32 {
  buf: [8]u32
  z: u32 = u32(0)
  while z < u32(8) {
    buf[z] = u32(0)
    z = z + u32(1)
  }
  ar: Arena = Arena { base: u32(0), count_at: u32(4), a: u64(1), b: u64(2), c: u64(3) }
  push_ab(ar, span(&buf))
  assert(buf[4] == u32(2))
  assert(buf[0] == u32(0x6261))
  assert(push_then_count(ar, span(&buf)) == u32(3))
  assert(buf[0] == u32(0x416261))
  push_n(ar, span(&buf), u32(2))
  assert(buf[4] == u32(5))
  assert(buf[1] == u32(0x7A))
  42
}
`

func TestE2ENativeCalleeEffects(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("callee_effects.oak", nativeCalleeEffectsProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_callee_effects", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native callee effects: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"set_count", "push_ab"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven equal to its Oak body in the span memory it writes (w)") {
			t.Errorf("%s must be proven in the span memory it writes; diagnostics:\n%s", fn, joined)
		}
	}
	// push_byte's read-modify-write under a shift is compared in its span
	// too; its diagrams may exceed the node budget, which is evidence, not
	// a trusted verdict.
	if !strings.Contains(joined, "asm unit push_byte (the span w): agrees with its Oak body on every witness input") && !strings.Contains(joined, "asm unit push_byte: proven equal to its Oak body in the span memory it writes (w)") {
		t.Errorf("push_byte must be decided in its span memory (proven or evidence); diagnostics:\n%s", joined)
	}
	if !strings.Contains(joined, "asm unit push_then_count: proven equal to its Oak body") || !strings.Contains(joined, "and the span memory it writes (w)") {
		t.Errorf("push_then_count must be proven in its result and its span memory; diagnostics:\n%s", joined)
	}
	if !strings.Contains(joined, "asm unit push_n: not verified (") {
		t.Errorf("push_n calls into a data-dependent loop and must stay trusted; diagnostics:\n%s", joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_callee_effects_c", New().WithSource("callee_effects.oak", nativeCalleeEffectsProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
