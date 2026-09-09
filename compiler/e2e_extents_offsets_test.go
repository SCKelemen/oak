package compiler

import (
	"strings"
	"testing"
)

// Extent facts, second increment: offset bounds (`i + 1 < len(v)` proves
// v[i] and v[i + 1]) and subslice extents (`subslice(v, 1, 3)` has exactly
// two elements for the rest of its block).
func TestE2EExtentOffsetsAndSubslice(t *testing.T) {
	src := `
pair_sum: (v: []u64): u64 {
  total: u64 = 0
  i: u32 = 0
  while i + u32(1) < len(v) {
    total = total + v[i] + v[i + u32(1)]
    i = i + u32(2)
  }
  total
}

main: (): i32 {
  regs: [4]u64
  regs[u32(0)] = u64(10)
  regs[u32(1)] = u64(20)
  regs[u32(2)] = u64(5)
  regs[u32(3)] = u64(7)
  v: []u64 = view(&regs)
  assert(pair_sum(v) == u64(42))
  s: []u64 = regs[u32(1):u32(3)]
  assert(s[u32(0)] + s[u32(1)] == u64(25))
  42
}
`
	output, err := New().WithSource("extents2.oak", src).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	// v[i], v[i + 1], s[0], s[1] proven; no view access stays checked.
	if got := strings.Count(output, ".base[ "); got != 4 {
		t.Fatalf("expected 4 proven view accesses, found %d:\n%s", got, output)
	}
	if strings.Contains(output, "oak_view_index_u64( ") {
		t.Fatalf("a proven view access remained checked:\n%s", output)
	}
	code, abnormal := buildAndRun(t, "extents2", src)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}

	// v[i + 2] under an i + 1 bound and s[2] on a two-element subslice
	// stay checked.
	over := `
beyond: (v: []u64): u64 {
  total: u64 = 0
  i: u32 = 0
  while i + u32(1) < len(v) {
    total = total + v[i + u32(2)]
    i = i + u32(1)
  }
  total
}

main: (): i32 {
  regs: [4]u64
  v: []u64 = view(&regs)
  s: []u64 = regs[u32(1):u32(3)]
  beyond(v) + s[u32(2)]
  42
}
`
	output, err = New().WithSource("extents3.oak", over).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	if strings.Count(output, "oak_view_index_u64( ") != 2 || strings.Contains(output, ".base[ ") {
		t.Fatalf("accesses beyond their facts must stay checked:\n%s", output)
	}
}
