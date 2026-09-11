package compiler

import (
	"strings"
	"testing"
)

// subslice(v, start, n) derives a view or span of the same kind: exactly n
// elements from start, one bounds check, zero copies; past-the-end traps.
// A literal n also establishes an extent fact for the rest of the block.
func TestE2ESubslice(t *testing.T) {
	src := `
tail_sum: (v: []u64): u64 {
  rest: []u64 = subslice(v, u32(1), u32(2))
  rest[u32(0)] + rest[u32(1)]
}

fill_tail: (s: [*]u64): u64 {
  rest: [*]u64 = subslice(s, u32(2), u32(2))
  rest[u32(0)] = u64(30)
  rest[u32(1)] = u64(7)
  rest[u32(0)] + rest[u32(1)]
}

main: (): i32 {
  regs: [4]u64
  regs[u32(1)] = u64(40)
  regs[u32(2)] = u64(2)
  v: []u64 = view(&regs)
  assert(tail_sum(v) == u64(42))
  buf: [4]u64
  s: [*]u64 = span(&buf)
  assert(fill_tail(s) == u64(37))
  42
}
`
	output, err := New().WithSource("subslice.oak", src).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	for _, want := range []string{"oak_view_subslice_u64( ", "oak_span_subslice_u64( "} {
		if !strings.Contains(output, want) {
			t.Fatalf("emitted C lacks %q:\n%s", want, output)
		}
	}
	// The literal length proves rest[0], rest[1] (views) and the two span
	// stores: no checked helper remains on the derived slices.
	if strings.Contains(output, "oak_view_index_u64( ") || strings.Contains(output, "oak_span_store_u64( ") || strings.Contains(output, "oak_span_index_u64( ") {
		t.Fatalf("accesses proven by the subslice extent must be direct:\n%s", output)
	}
	code, abnormal := buildAndRun(t, "subslice", src)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// Past-the-end derivation traps, and a constant beyond the literal length
// stays checked.
func TestE2ESubsliceBounds(t *testing.T) {
	over := `
main: (): i32 {
  regs: [4]u64
  v: []u64 = view(&regs)
  rest: []u64 = subslice(v, u32(3), u32(2))
  assert(rest[u32(0)] == u64(0))
  42
}
`
	code, abnormal := buildAndRun(t, "subsliceover", over)
	if !abnormal && code == 42 {
		t.Fatal("subslice past the end must trap")
	}

	checked := `
main: (): i32 {
  regs: [4]u64
  v: []u64 = view(&regs)
  rest: []u64 = subslice(v, u32(1), u32(2))
  assert(rest[u32(2)] == u64(0))
  42
}
`
	output, err := New().WithSource("subslicechecked.oak", checked).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	if !strings.Contains(output, "oak_view_index_u64( ") {
		t.Fatalf("rest[2] beyond a two-element subslice must stay checked:\n%s", output)
	}
}
