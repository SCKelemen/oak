package compiler

import (
	"strings"
	"testing"
)

// The OS pilot's second round (docs/notes/os-language-requests-2026-09.md,
// round two). R11: an aggregate element of an owned array — a row of a
// grid, a record — is selected in place behind the checked index, never
// copied out of the ternary. R3 residual: the page-table walk's masked,
// narrowed index is proven by its mask, directly and through a binding.
func TestE2EOSRound2AggregateElementsInPlace(t *testing.T) {
	src := `
Row: type = struct { cells: [4]u64, tag: u32 }

grid_at: (g: [3][4]u64, i: u32, j: u32): u64 = g[i][j]
row_tag: (rows: [3]Row, i: u32): u32 = rows[i].tag
row_cell: (rows: [3]Row, i: u32, j: u32): u64 = rows[i].cells[j]

main: (): i32 {
  g: [3][4]u64 = [[1, 2, 3, 4], [5, 6, 7, 8], [9, 10, 11, 12]]
  rows: [3]Row = [Row { cells: [1, 2, 3, 4], tag: 7 }, Row { cells: [5, 6, 7, 8], tag: 8 }, Row { cells: [9, 10, 11, 12], tag: 9 }]
  grid_at(g, 1, 2) == u64(7) && row_tag(rows, 2) == u32(9) && row_cell(rows, 1, 3) == u64(8) ? 42 | 1
}
`
	emitted, err := New().WithSource("agg.oak", src).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"oak_index( g.v[ oak_lv_idx( (u64)( i ), 3 ) ].v, 4, (u64)( j ) )",
		"rows.v[ oak_lv_idx( (u64)( i ), 3 ) ].tag",
		"oak_index( rows.v[ oak_lv_idx( (u64)( i ), 3 ) ].cells.v, 4, (u64)( j ) )",
	} {
		if !strings.Contains(emitted, want) {
			t.Errorf("expected the element selected in place:\n%s\nin:\n%s", want, emitted)
		}
	}
	for _, copied := range []string{"oak_index( g.v,", "oak_index( rows.v,"} {
		if strings.Contains(emitted, copied) {
			t.Errorf("an aggregate element is copied out of the checked index: %q", copied)
		}
	}
	if code, abnormal := buildAndRun(t, "os_round2_agg", src); abnormal || code != 42 {
		t.Fatalf("expected exit 42, got %d (abnormal %v)", code, abnormal)
	}
	// The in-place selection is still checked.
	bad := strings.Replace(src, "grid_at(g, 1, 2) == u64(7)", "grid_at(g, 3, 2) == u64(7)", 1)
	if _, abnormal := buildAndRun(t, "os_round2_agg_bad", bad); !abnormal {
		t.Fatalf("expected the out-of-range row to trap")
	}
}

func TestE2EOSRound2MaskedWalkIndex(t *testing.T) {
	src := `
walk: (table: [512]u64, va: u64): u64 = table[u32_trunc_u64((va >> 12) & 511)]

walk_bound: (table: [512]u64, va: u64): u64 {
  idx: u32 = u32_trunc_u64((va >> 21) & 511)
  table[idx]
}

walk_sat: (table: [512]u64, va: u64): u64 = table[u32_saturating_u64(va & 511)]

walk_wide: (table: [512]u64, va: u32): u64 = table[u64(va & u32(511))]

near_miss_mask: (table: [512]u64, va: u64): u64 = table[u32_trunc_u64(va & 512)]

near_miss_rebound: (table: [512]u64, va: u64): u64 {
  idx: u32 = u32_trunc_u64((va >> 21) & 511)
  idx = idx + u32(1)
  table[idx]
}

main: (): i32 {
  t: [512]u64
  t[u32(1)] = u64(5)
  t[u32(2)] = u64(7)
  w: u64 = walk(t, u64(4096)) + walk_bound(t, u64(4194304)) + walk_sat(t, u64(1)) + walk_wide(t, u32(2))
  w == u64(24) && near_miss_mask(t, u64(0)) == u64(0) && near_miss_rebound(t, u64(0)) == u64(5) ? 42 | 1
}
`
	emitted, err := New().WithSource("walk.oak", src).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"table.v[ oak_conv_u32_trunc_u64( ( oak_shr_u64( va, 12 ) & 511 ) ) ]",
		"table.v[ idx ]",
		"table.v[ oak_conv_u32_saturating_u64( ( va & 511 ) ) ]",
		"table.v[ ((u64)( ( va & ((u32)( 511 )) ) )) ]",
	} {
		if !strings.Contains(emitted, want) {
			t.Errorf("expected the masked index proven:\n%s\nin:\n%s", want, emitted)
		}
	}
	if got := strings.Count(emitted, "oak_index( table.v, 512,"); got != 2 {
		t.Errorf("expected exactly the two near misses checked, found %d oak_index sites:\n%s", got, emitted)
	}
	if code, abnormal := buildAndRun(t, "os_round2_walk", src); abnormal || code != 42 {
		t.Fatalf("expected exit 42, got %d (abnormal %v)", code, abnormal)
	}
}
