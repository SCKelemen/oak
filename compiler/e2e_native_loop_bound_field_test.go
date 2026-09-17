package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// A loop marks the span memories its body can write, and no others
// (docs/spec/94-assembler.md §8 "A loop marks what it can write"). A
// read-only body marked every writable memory, so its continue
// condition and its reads saw the loop's unknown memory where the
// machine side saw the entry memory, and a loop bounded by a field of
// the element it reads — `while i < s[d].count` — came back witnessed
// rather than proven though nothing wrote that field.
const nativeLoopBoundFieldProgram = `
Dom: type = struct { xs: [4]u32, count: u32 }

// The bound is a field of the element the body reads.
by_count: (s: [*]Dom, d: u32): u32 {
  total: u32 = 0
  d < len(s) ? {
    i: u32 = 0
    while i < s[d].count && i < u32(4) {
      total = total + s[d].xs[i]
      i = i + u32(1)
    }
  } | { }
  total
}

// The body does store, so its memory is marked as before.
fill: (s: [*]Dom, d: u32, v: u32): () {
  d < len(s) ? {
    i: u32 = 0
    while i < u32(4) {
      s[d].xs[i] = v + i
      i = i + u32(1)
    }
  } | { }
}

main: (): i32 {
  doms: [2]Dom
  fill(span(&doms), u32(0), u32(10))
  fill(span(&doms), u32(1), u32(20))
  doms[u32(0)].count = u32(3)
  doms[u32(1)].count = u32(1)
  // dom 0: 10 + 11 + 12 = 33 over three of four; dom 1: 20 over one.
  i32_bits_u32((by_count(span(&doms), u32(0)) + by_count(span(&doms), u32(1))) & u32(255))
}
`

func TestE2ENativeLoopBoundByAField(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("loop_bound.oak", nativeLoopBoundFieldProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_loop_bound_field", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 53 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 53\n%s", code, abnormal, joined)
	}
	// The read-only loop is proven by coupling, not merely witnessed.
	if !strings.Contains(joined, "asm unit by_count: proven equal to its Oak body at the bit level — data-dependent loop coupled inductively") {
		t.Errorf("by_count must be proven by coupling; diagnostics:\n%s", joined)
	}
	// The storing loop still marks the memory it writes.
	if !strings.Contains(joined, "asm unit fill: proven equal to its Oak body in the span memory it writes (s.xs)") {
		t.Errorf("fill must be proven in the memory it writes; diagnostics:\n%s", joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_loop_bound_field_c", New().WithSource("loop_bound.oak", nativeLoopBoundFieldProgram)); abnormal || code != 53 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 53", code, abnormal)
	}
}
