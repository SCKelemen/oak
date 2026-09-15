package compiler

import (
	"strings"
	"testing"
)

// Three ways a length reaches a constant index (docs/spec/50-borrowing.md,
// extent facts): an `assert(len(v) == K)` before the block that indexes
// (Oak.Extents.exact_length_min), a binding declared as the length and
// tested by name (`n: u32 = len(src)`, `n >= u32(4)`), and `len(v) == K`
// as a `?` condition. Each proven access is emitted as a direct read in C.
const extentsAssertAliasProgram = `
first_of_one: (state: []u64): u64 {
  assert(len(state) == u32(1))
  state[0]
}

bom_of: (src: []u8): u32 {
  n: u32 = len(src)
  n >= u32(4) && src[0] == u8(255) && src[1] == u8(254) && src[2] == u8(0) && src[3] == u8(0) ? u32(4) | u32(0)
}

pair_sum: (v: []u32): u32 = len(v) == u32(2) ? v[0] + v[1] | u32(0)

main: (): i32 {
  one: [1]u64 = [1]u64{u64(42)}
  assert(first_of_one(view(&one)) == u64(42))
  bom: [4]u8 = [4]u8{u8(255), u8(254), u8(0), u8(0)}
  assert(bom_of(view(&bom)) == u32(4))
  short: [2]u8 = [2]u8{u8(255), u8(254)}
  assert(bom_of(view(&short)) == u32(0))
  pair: [2]u32 = [2]u32{u32(40), u32(2)}
  assert(pair_sum(view(&pair)) == u32(42))
  42
}
`

func TestE2EExtentsAssertAndLengthAlias(t *testing.T) {
	output, err := New().WithSource("extents_alias.oak", extentsAssertAliasProgram).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	// state[0]; src[0..3]; v[0], v[1]: seven proven reads.
	if got := strings.Count(output, ".base[ "); got != 7 {
		t.Fatalf("expected 7 proven view accesses, found %d:\n%s", got, output)
	}
	if strings.Contains(output, "oak_view_index_u64( ") || strings.Contains(output, "oak_view_index_u8( ") || strings.Contains(output, "oak_view_index_u32( ") {
		t.Fatalf("a proven view access remained checked:\n%s", output)
	}
	code, abnormal := buildAndRun(t, "extents_alias", extentsAssertAliasProgram)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
