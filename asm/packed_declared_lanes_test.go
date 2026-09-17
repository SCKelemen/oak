package asm

import (
	"fmt"
	"math/rand"
	"testing"
)

// Result-area copies pack widened record leaves without explicit masks:
// zeroExtend keeps a parameter's declared width. Reloading a byte from
// that word must recover the original leaf before loop coupling searches
// for its image among the other record fields.
func TestSubstitutePackedDeclaredLanes(t *testing.T) {
	rng := rand.New(rand.NewSource(32))
	for _, width := range []int{8, 16, 32} {
		var lanes []*term
		word := constTerm(0, 64)
		for k := 0; k < 64/width; k++ {
			lane := paramTerm(fmt.Sprintf("state.block[%d]", k), width)
			lanes = append(lanes, lane)
			placed := zeroExtend(lane, 64)
			if k > 0 {
				placed = binaryTerm("shl", placed, constTerm(uint64(k*width), 64))
			}
			word = binaryTerm("or", word, placed)
		}
		for k, lane := range lanes {
			for _, resultWidth := range []int{width, 64} {
				extracted := truncate(binaryTerm("shr", word, constTerm(uint64(k*width), 64)), width)
				extracted = adaptWidth(extracted, resultWidth)
				got := substitute(extracted, nil)
				if want := adaptWidth(lane, resultWidth); !equalTerms(got, want) {
					t.Fatalf("lane %d at %d bits, result %d: got %s, want %s", k, width, resultWidth, got, want)
				}
				for range 64 {
					env := map[string]uint64{}
					for _, leaf := range lanes {
						env[leaf.name] = rng.Uint64() & mask(width)
					}
					if got.eval(env) != extracted.eval(env) {
						t.Fatalf("lane %d at %d bits changed value", k, width)
					}
				}
			}
		}
	}
}

func TestUnpackDeclaredLanesRefusesOverlapAndWrongWidths(t *testing.T) {
	byte0 := zeroExtend(paramTerm("a", 8), 64)
	byte1 := zeroExtend(paramTerm("b", 8), 64)
	for _, tc := range []struct {
		name string
		word *term
	}{
		{"bare scalar adapter", byte0},
		{"overlapping placements", binaryTerm("or", byte0, byte1)},
		{"unbounded low word", binaryTerm("or", paramTerm("wide", 64), binaryTerm("shl", byte1, constTerm(8, 64)))},
		{"unbounded high word", binaryTerm("or", byte0, binaryTerm("shl", paramTerm("wide", 64), constTerm(8, 64)))},
		{"misaligned lane", binaryTerm("or", byte0, binaryTerm("shl", byte1, constTerm(7, 64)))},
		{"wrapping shift", binaryTerm("shl", byte1, constTerm(64, 64))},
		{"narrow shift", &term{kind: termBinary, width: 32, op: "shl", left: zeroExtend(paramTerm("b", 8), 32), right: constTerm(32, 32)}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			if got, ok := unpackLane(tc.word, 8, 8); ok {
				t.Fatalf("inexact pack must be refused, got %s", got)
			}
		})
	}
}
