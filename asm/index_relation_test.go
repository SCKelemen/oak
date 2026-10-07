package asm

import (
	"math/rand"
	"testing"
)

// Check the congruence shortcut against complete valuations at small widths,
// including modular overflow, negative coefficient differences, and shared
// terms that cancel. Unknown is always allowed; an incorrect fact is not.
func TestLinearIndexRelationExhaustive(t *testing.T) {
	rng := rand.New(rand.NewSource(641))
	for width := 1; width <= 6; width++ {
		m := mask(width)
		for sample := 0; sample < 150; sample++ {
			a := &linearForm{width: width, coeffs: map[string]uint64{"x": rng.Uint64() & m, "y": rng.Uint64() & m}, constant: rng.Uint64() & m}
			b := &linearForm{width: width, coeffs: map[string]uint64{"x": rng.Uint64() & m, "y": rng.Uint64() & m}, constant: rng.Uint64() & m}
			if sample%3 == 0 {
				b.coeffs["x"] = a.coeffs["x"]
			}
			known, equal := linearFormsRelate(a, b)
			if !known {
				continue
			}
			for x := uint64(0); x <= m; x++ {
				for y := uint64(0); y <= m; y++ {
					av := (a.constant + a.coeffs["x"]*x + a.coeffs["y"]*y) & m
					bv := (b.constant + b.coeffs["x"]*x + b.coeffs["y"]*y) & m
					if (av == bv) != equal {
						t.Fatalf("width %d: %v vs %v at (%d,%d): false relation", width, a, b, x, y)
					}
				}
			}
		}
	}
}

func TestMemoryAtModularDisjointnessAndOverwrite(t *testing.T) {
	x, y, base := paramTerm("x", 32), paramTerm("y", 32), paramTerm("base", 32)
	index := binaryTerm("add", base, binaryTerm("shl", x, constTerm(2, 32)))
	other := binaryTerm("add", base, binaryTerm("add", binaryTerm("shl", y, constTerm(2, 32)), constTerm(1, 32)))
	original := paramTerm("original", 32)
	if got := memoryAt([]*spanWrite{{index: other, value: constTerm(9, 32)}}, index, original); got != original {
		t.Fatal("different residues modulo four must not alias, even on overflow")
	}
	guard := paramTerm("guard", 1)
	log := []*spanWrite{
		{index: y, value: constTerm(1, 32)},
		{index: index, value: constTerm(2, 32)},
		{index: index, value: constTerm(3, 32), guard: guard},
	}
	got := memoryAt(log, index, original)
	for _, v := range []uint64{0, 1, 0xffffffff} {
		for g := uint64(0); g < 2; g++ {
			env := map[string]uint64{"x": v, "y": v, "base": 0xffffffff, "guard": g}
			if value := got.eval(env); value != 2+g {
				t.Fatalf("guard %d: got %d", g, value)
			}
		}
	}
	// Distinct memory snapshots cannot become the same linear atom.
	a := selectTerm("before", x, 32).linearAt(32)
	b := selectTerm("after", x, 32).linearAt(32)
	if known, _ := linearFormsRelate(a, b); known {
		t.Fatal("independent memories were related")
	}
	for _, width := range []int{32, 64} {
		a := &linearForm{width: width, coeffs: map[string]uint64{"x": 4}, constant: mask(width)}
		b := &linearForm{width: width, coeffs: map[string]uint64{"y": 4}, constant: 0}
		if known, equal := linearFormsRelate(a, b); !known || equal {
			t.Fatalf("width %d: wrapped residue not disjoint", width)
		}
		b.width = 16
		if known, _ := linearFormsRelate(a, b); known {
			t.Fatal("different widths related")
		}
	}
}

func BenchmarkMemoryAtOverwrite(b *testing.B) {
	index := paramTerm("index", 32)
	log := make([]*spanWrite, 1000)
	for i := range log {
		log[i] = &spanWrite{index: paramTerm("older", 32), value: constTerm(uint64(i), 32)}
	}
	log[len(log)-1] = &spanWrite{index: index, value: constTerm(7, 32)}
	base := paramTerm("initial", 32)
	b.ReportAllocs()
	for b.Loop() {
		if memoryAt(log, index, base).eval(nil) != 7 {
			b.Fatal("wrong read")
		}
	}
}
