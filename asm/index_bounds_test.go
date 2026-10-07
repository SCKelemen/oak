package asm

import (
	"math/rand"
	"testing"
)

// Independently evaluate mixed-width DAGs under every small input valuation.
// This exercises truncation, overflow, ITE joins, and unsupported operations.
func TestIndexBoundsExhaustive(t *testing.T) {
	rng := rand.New(rand.NewSource(8027))
	for width := 1; width <= 6; width++ {
		terms := []*term{paramTerm("x", width), paramTerm("y", width)}
		for i := 0; i < 180; i++ {
			w := 1 + rng.Intn(6)
			l, r := terms[rng.Intn(len(terms))], terms[rng.Intn(len(terms))]
			var n *term
			switch i % 5 {
			case 0:
				n = constTerm(rng.Uint64(), w)
			case 1:
				n = &term{kind: termIte, width: w, cond: paramTerm("g", 1), left: l, right: r}
			default:
				ops := []string{"add", "sub", "and", "or", "xor", "mul", "shl", "shr"}
				op := ops[rng.Intn(len(ops))]
				if op == "shl" || op == "shr" {
					r = constTerm(uint64(rng.Intn(w)), w)
				}
				n = &term{kind: termBinary, width: w, op: op, left: l, right: r}
			}
			terms = append(terms, n)
		}
		bounds := map[*term]indexBounds{}
		for x := uint64(0); x <= mask(width); x++ {
			for y := uint64(0); y <= mask(width); y++ {
				for g := uint64(0); g < 2; g++ {
					env := map[string]uint64{"x": x, "y": y, "g": g}
					eval := mapMemo{}
					for _, n := range terms {
						for _, w := range []int{n.width, 3, 32} {
							b := boundsAt(n, w, bounds)
							value := eval.eval(n, env) & mask(w)
							if value < b.lo || value > b.hi {
								t.Fatalf("input width %d, term %s at width %d, env %v: %d outside %+v", width, n, w, env, value, b)
							}
						}
					}
				}
			}
		}
	}
}

func TestIndexBoundsWordEdges(t *testing.T) {
	for _, w := range []int{32, 64} {
		x := binaryTerm("and", paramTerm("x", w), constTerm(255, w))
		cases := []struct {
			name   string
			n      *term
			lo, hi uint64
		}{
			{"bounded add", binaryTerm("add", x, constTerm(256, w)), 256, 511},
			{"wrapping add", binaryTerm("add", x, constTerm(mask(w), w)), 0, mask(w)},
			{"bounded sub", binaryTerm("sub", constTerm(511, w), x), 256, 511},
			{"underflow", binaryTerm("sub", x, constTerm(1, w)), 0, mask(w)},
		}
		for _, c := range cases {
			b := boundsAt(c.n, w, map[*term]indexBounds{})
			if b.lo != c.lo || b.hi != c.hi {
				t.Fatalf("%d %s: %+v", w, c.name, b)
			}
		}
	}
	// The native 64-bit addition wraps only when viewed as a 32-bit index.
	n := binaryTerm("add", binaryTerm("and", paramTerm("x", 64), constTerm(255, 64)), constTerm(0xffffffff, 64))
	b := boundsAt(n, 32, map[*term]indexBounds{})
	if b.lo != 0 || b.hi != 0xffffffff {
		t.Fatalf("truncation retained a non-wrapping interval: %+v", b)
	}
}

func TestMemoryAtBoundedRegions(t *testing.T) {
	x, y := paramTerm("x", 32), paramTerm("y", 32)
	low := binaryTerm("and", x, constTerm(255, 32))
	high := binaryTerm("add", constTerm(256, 32), binaryTerm("and", y, constTerm(255, 32)))
	initial := paramTerm("initial", 32)
	for _, guard := range []*term{nil, paramTerm("g", 1)} {
		if got := memoryAt([]*spanWrite{{index: high, value: constTerm(9, 32), guard: guard}}, low, initial); got != initial {
			t.Fatal("disjoint bounded region kept an alias test")
		}
	}
	// Check overlapping and wrapping ranges against concrete store semantics,
	// including equal indices at the boundary and a guarded store.
	for _, offset := range []uint64{0, 255, 256, 0xffffffff} {
		at := binaryTerm("add", constTerm(offset, 32), binaryTerm("and", y, constTerm(255, 32)))
		got := memoryAt([]*spanWrite{{index: at, value: constTerm(9, 32), guard: paramTerm("g", 1)}}, low, initial)
		for xv := uint64(0); xv < 256; xv++ {
			for yv := uint64(0); yv < 256; yv++ {
				for g := uint64(0); g < 2; g++ {
					env := map[string]uint64{"x": xv, "y": yv, "g": g, "initial": 7}
					want := uint64(7)
					if g != 0 && xv == (offset+yv)&0xffffffff {
						want = 9
					}
					if value := got.eval(env); value != want {
						t.Fatalf("offset %d x %d y %d guard %d: got %d want %d", offset, xv, yv, g, value, want)
					}
				}
			}
		}
	}
	// A snapshot replaces the underlying memory even when the later store is
	// disjoint. It must not disappear along with that store.
	got := memoryAt([]*spanWrite{{memory: "after"}, {index: high, value: constTerm(9, 32)}}, low, initial)
	if got.kind != termSelect || got.name != "after" {
		t.Fatal("lost memory snapshot")
	}
}
