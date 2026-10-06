package asm

import "testing"

// A whole-record copy loads `Surface { id: u32, tags: u32, alive: u8,
// hue: u32 }` as two words; the second covers alive, three padding bytes,
// and hue. The bytes no leaf's cell covers are padding and read as gaps;
// a range that starts or ends inside a field's cell is still refused.
func TestTileLeavesOrPaddingAdmitsOnlyPadding(t *testing.T) {
	arg := newRecordSpanArg(16, []compositeLeaf{
		{name: ".id", offset: 0, width: 32},
		{name: ".tags", offset: 4, width: 32},
		{name: ".alive", offset: 8, width: 8},
		{name: ".hue", offset: 12, width: 32},
	})
	leaves, at, gaps, ok := arg.tileLeavesOrPadding(8, 8)
	if !ok || len(leaves) != 2 || leaves[0].name != ".alive" || leaves[1].name != ".hue" || at[0] != 0 || at[1] != 4 {
		t.Fatalf("alive, padding, hue: leaves %v at %v ok %v", leaves, at, ok)
	}
	if len(gaps) != 1 || gaps[0] != [2]int64{1, 3} {
		t.Fatalf("the padding is bytes 1..3 of the word, got %v", gaps)
	}
	if _, _, gaps, ok := arg.tileLeavesOrPadding(0, 8); !ok || len(gaps) != 0 {
		t.Fatalf("id and tags tile exactly with no padding: gaps %v ok %v", gaps, ok)
	}
	for _, r := range [][2]int64{{2, 8}, {10, 4}, {12, 2}, {6, 4}} {
		if _, _, _, ok := arg.tileLeavesOrPadding(r[0], r[1]); ok {
			t.Errorf("[%d, +%d) starts or ends inside a field and must be refused", r[0], r[1])
		}
	}
	if _, _, _, ok := arg.tileLeavesOrPadding(9, 3); ok {
		t.Errorf("padding alone is no field access")
	}
}
