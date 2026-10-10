package asm

import "testing"

// The atom walk is only an input to component ordering. Exercise the actual
// implication decision as well as the ordered-leaf differential tests. Separate
// blasters already have map-order-dependent representatives, so compare logical
// decisions rather than requiring their private variable numbers to match.
func TestComponentAtomsProofAndRefutationDifferential(t *testing.T) {
	type obligation struct {
		name          string
		names         []string
		widths        map[string]int
		premise, a, b *term
		width         int
		want          bool
	}
	x, y, flag := paramTerm("x", 8), paramTerm("y", 8), paramTerm("flag", 1)
	x16, y16 := zeroExtend(x, 16), paramTerm("y16", 16)
	i, j := paramTerm("i", 4), paramTerm("j", 4)
	leftRead, rightRead := selectTerm("mem", i, 8), selectTerm("mem", j, 8)
	shared := flag
	for k := 0; k < 16; k++ {
		shared = &term{kind: termBinary, width: 1, op: "or", left: shared, right: flag}
	}
	scalarPremise := binaryTerm("and", cmpTerm("eq", x, y), shared)
	mixedPremise := binaryTerm("and", cmpTerm("eq", x16, y16), shared)
	readPremise := binaryTerm("and", cmpTerm("eq", i, j), shared)
	cases := []obligation{
		{"equal", []string{"flag", "x", "y"}, map[string]int{"flag": 1, "x": 8, "y": 8}, scalarPremise, x, y, 8, true},
		{"wrong_bit", []string{"flag", "x", "y"}, map[string]int{"flag": 1, "x": 8, "y": 8}, scalarPremise, x, binaryTerm("xor", y, constTerm(1, 8)), 8, false},
		{"changed_assumption", []string{"flag", "x", "y"}, map[string]int{"flag": 1, "x": 8, "y": 8}, binaryTerm("and", cmpTerm("ne", x, y), shared), x, y, 8, false},
		{"mixed_width", []string{"flag", "x", "y16"}, map[string]int{"flag": 1, "x": 8, "y16": 16}, mixedPremise, zeroExtend(x, 32), zeroExtend(y16, 32), 32, true},
		{"mixed_width_wrong_high_bit", []string{"flag", "x", "y16"}, map[string]int{"flag": 1, "x": 8, "y16": 16}, mixedPremise, zeroExtend(x, 32), binaryTerm("xor", zeroExtend(y16, 32), constTerm(256, 32)), 32, false},
		{"equal_read_indices", []string{"flag", "i", "j"}, map[string]int{"flag": 1, "i": 4, "j": 4}, readPremise, leftRead, rightRead, 8, true},
		{"wrong_read_value", []string{"flag", "i", "j"}, map[string]int{"flag": 1, "i": 4, "j": 4}, readPremise, leftRead, binaryTerm("xor", rightRead, constTerm(1, 8)), 8, false},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			for repeat := 0; repeat < 8; repeat++ {
				old := componentBlasterWithAtoms(tc.names, tc.widths, tc.premise, tc.a, tc.b, referenceComponentAtomWalk)
				memoized := componentBlaster(tc.names, tc.widths, tc.premise, tc.a, tc.b)
				if old == nil || memoized == nil {
					t.Fatal("fixture must retain separate components")
				}
				oldHolds, oldDecided := impliesEqualUnder(old, tc.premise, tc.a, tc.b, tc.width)
				newHolds, newDecided := impliesEqualUnder(memoized, tc.premise, tc.a, tc.b, tc.width)
				if !oldDecided || oldHolds != tc.want {
					t.Fatalf("reference: holds=%v decided=%v, want holds=%v", oldHolds, oldDecided, tc.want)
				}
				if newHolds != oldHolds || newDecided != oldDecided {
					t.Fatalf("memoized: holds=%v decided=%v; reference: holds=%v decided=%v", newHolds, newDecided, oldHolds, oldDecided)
				}
			}
		})
	}
}

func TestComponentAtomsReadPlacementDifferential(t *testing.T) {
	index := paramTerm("idx", 32)
	otherIndex := paramTerm("idx", 32) // Same value spelling, distinct read identity.
	x, y, z := paramTerm("x", 8), paramTerm("y", 8), paramTerm("z", 8)
	first := selectTerm("mem", index, 8)
	duplicate := selectTerm("mem", index, 8)
	distinct := selectTerm("mem", otherIndex, 8)
	otherSpan := selectTerm("other", index, 8)
	premise := cmpTerm("eq", first, x)
	for _, part := range []*term{
		cmpTerm("eq", duplicate, x), cmpTerm("eq", distinct, z), cmpTerm("eq", otherSpan, z),
	} {
		premise = &term{kind: termBinary, op: "and", width: 1, left: premise, right: part}
	}
	names := []string{"idx", "x", "y", "z"}
	widths := map[string]int{"idx": 32, "x": 8, "y": 8, "z": 8}
	for _, mode := range []struct {
		name string
		walk func(*term, func(*term))
	}{
		{"original", referenceComponentAtomWalk},
		{"memoized", newComponentAtoms().walk},
		{"capped", newComponentAtomsWithLimits(2, 1).walk},
	} {
		t.Run(mode.name, func(t *testing.T) {
			bl := componentBlasterWithAtoms(names, widths, premise, x, y, mode.walk)
			if bl == nil {
				t.Fatal("fixture must retain separate components")
			}
			xBlock, zBlock := bl.blockOf["x"], bl.blockOf["z"]
			if xBlock == zBlock || bl.blockOf["idx"] == xBlock || bl.blockOf["idx"] == zBlock {
				t.Fatal("read values were joined to independent values or their index")
			}
			for _, want := range []struct {
				span  string
				index *term
				block string
			}{{"mem", index, xBlock}, {"mem", otherIndex, zBlock}, {"other", index, zBlock}} {
				if block, known := bl.readBlock(want.span, want.index); !known || block != want.block {
					t.Fatalf("read placement: known=%v block=%q, want %q", known, block, want.block)
				}
			}
			if _, known := bl.readBlock("mem", paramTerm("idx", 32)); known {
				t.Fatal("unseen index pointer inherited a read placement")
			}
			if _, known := bl.readBlock("unseen", index); known {
				t.Fatal("unseen span inherited a read placement")
			}
			if bl.blockReserved[xBlock] != 3 || bl.blockReserved[zBlock] != 4 {
				t.Fatalf("reserved slots x=%d z=%d, want one/two reads plus two spare slots", bl.blockReserved[xBlock], bl.blockReserved[zBlock])
			}
		})
	}
}
