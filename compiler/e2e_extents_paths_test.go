package compiler

import (
	"strings"
	"testing"
)

// Extent facts over field paths (docs/spec/50-borrowing.md): a container or
// an index may be a record field path — `t.block[t.filled]` under
// `t.filled < 64`, `t.h[j]` under `j < 8` — and a fact dies when the path or
// any prefix of it (the record itself) is assigned. This is the shape of a
// hash state's partial block and of a page's slot table.
func TestE2EExtentFieldPaths(t *testing.T) {
	src := `
State: type = struct { block: [64]u8, filled: u32, h: [8]u32 }

pad: (s: State): State {
  t: State = s
  while t.filled < u32(64) {
    t.block[t.filled] = u8(0)
    t.filled = t.filled + u32(1)
  }
  k: u32 = 0
  while k < u32(8) {
    t.block[u32(56) + k] = u8(7)
    k = k + u32(1)
  }
  j: u32 = 0
  while j < u32(8) {
    t.h[j] = t.h[j] + u32(j)
    j = j + u32(1)
  }
  t
}

main: (): i32 {
  s: State
  s.h = [8]u32{ 0, 0, 0, 0, 0, 0, 0, 0 }
  s.filled = u32(60)
  p: State = pad(s)
  i32_bits_u32(u32(p.block[u32(63)]) + p.h[u32(7)] + u32(28))
}
`
	output, err := New().WithSource("extents5.oak", src).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	// pad's five accesses are proven: no checked owned-array read or store
	// remains anywhere but main's, which index a record it just declared.
	if got := strings.Count(output, "oak_index( "); got != 0 {
		t.Fatalf("expected no checked owned-array reads, found %d:\n%s", got, output)
	}
	if got := strings.Count(output, "oak_store( "); got != 0 {
		t.Fatalf("expected no checked owned-array stores, found %d:\n%s", got, output)
	}
	code, abnormal := buildAndRun(t, "extents5", src)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}

	// The record reassigned inside the loop kills the path fact before the
	// access; a field index without a bound stays checked.
	over := `
State: type = struct { block: [64]u8, filled: u32 }

reset: (s: State, other: State): State {
  t: State = s
  while t.filled < u32(64) {
    t = other
    t.block[t.filled] = u8(0)
    t.filled = t.filled + u32(1)
  }
  t
}

poke: (s: State): u8 {
  t: State = s
  t.block[t.filled]
}

main: (): i32 = 0
`
	output, err = New().WithSource("extents5over.oak", over).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	if got := strings.Count(output, "oak_store( "); got != 1 {
		t.Fatalf("expected the reset store to stay checked, found %d:\n%s", got, output)
	}
	if got := strings.Count(output, "oak_index( "); got != 1 {
		t.Fatalf("expected the unbounded read to stay checked, found %d:\n%s", got, output)
	}
}
