package compiler

import (
	"strings"
	"testing"
)

// Extent facts (typechecker/extents.go): a check the program already
// performs proves the accesses it dominates, and the backend elides their
// bounds checks; every unproven neighbor stays checked. Verified in the
// emitted C (direct `.base[` / `regs[` vs the checked helpers) and by
// native execution.
func TestE2EExtentFactsElideProvenChecks(t *testing.T) {
	src := `
sum_view: (v: []u64): u64 {
  total: u64 = 0
  i: u32 = 0
  while i < len(v) {
    total = total + v[i]
    i = i + u32(1)
  }
  total
}

dot: (a: []u64, b: []u64): u64 {
  acc: u64 = 0
  len(a) == len(b) ? {
    i: u32 = 0
    while i < len(a) {
      acc = acc + a[i] * b[i]
      i = i + u32(1)
    }
  }
  acc
}

third_or_zero: (v: []u64): u64 {
  len(v) >= u32(4) ? v[u32(3)] | u64(0)
}

main: (): i32 {
  regs: [4]u64
  regs[u32(0)] = u64(1)
  regs[u32(1)] = u64(2)
  regs[u32(2)] = u64(3)
  regs[u32(3)] = u64(36)
  v: []u64 = view(&regs)
  assert(sum_view(v) == u64(42))
  assert(dot(v, v) == u64(1310))
  assert(third_or_zero(v) == u64(36))
  pair: [2]u64
  sv: []u64 = view(&pair)
  assert(third_or_zero(sv) == u64(0))
  42
}
`
	output, err := New().WithSource("extents.oak", src).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	// Proven: v[i] in the loop, a[i] and b[i] under the same-length fact,
	// v[3] under the min-length fact, the four constant stores into regs.
	if got := strings.Count(output, ".base[ "); got != 4 {
		t.Fatalf("expected 4 proven view accesses, found %d:\n%s", got, output)
	}
	if strings.Contains(output, "oak_view_index_u64( ") {
		t.Fatalf("a proven view access remained checked:\n%s", output)
	}
	if strings.Contains(output, "oak_store( ") {
		t.Fatalf("constant stores into a static array must be proven:\n%s", output)
	}
	code, abnormal := buildAndRun(t, "extents", src)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// Negative controls: an index reassigned before its use, a container
// reassigned inside the scope, and a non-literal bound derive no facts —
// those accesses stay checked, and an out-of-range one still traps.
func TestE2EExtentFactsStayChecked(t *testing.T) {
	src := `
shifted: (v: []u64): u64 {
  total: u64 = 0
  i: u32 = 0
  while i < len(v) {
    i = i + u32(1)
    total = total + v[i]
  }
  total
}

main: (): i32 {
  regs: [4]u64
  v: []u64 = view(&regs)
  shifted(v)
  42
}
`
	output, err := New().WithSource("unproven.oak", src).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	if !strings.Contains(output, "oak_view_index_u64( ") || strings.Contains(output, ".base[ ") {
		t.Fatalf("an access after the index was reassigned must stay checked:\n%s", output)
	}
	code, abnormal := buildAndRun(t, "unproven", src)
	if !abnormal && code == 42 {
		t.Fatal("the unproven out-of-range access must trap, not succeed")
	}

	bounded := `
peek: (v: []u64, n: u32): u64 {
  len(v) >= n ? v[u32(3)] | u64(0)
}
main: (): i32 {
  regs: [4]u64
  v: []u64 = view(&regs)
  peek(v, u32(4))
  42
}
`
	output, err = New().WithSource("nonliteral.oak", bounded).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	if !strings.Contains(output, "oak_view_index_u64( ") {
		t.Fatalf("a non-literal bound must not prove a constant access:\n%s", output)
	}
}
