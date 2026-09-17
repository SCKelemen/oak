package asm

import (
	"fmt"
	"math/rand"
	"testing"
)

func TestCanonicalBitwiseRotate(t *testing.T) {
	rng := rand.New(rand.NewSource(17))
	for _, width := range []int{32, 64} {
		for _, count := range []uint64{0, 1, 7, 8, 12, 16, 31, 32, 33, 63, 64, 65, ^uint64(0)} {
			t.Run(fmt.Sprintf("w%d_k%d", width, count), func(t *testing.T) {
				x := paramTerm("x", width)
				original := binaryTerm("ror", x, constTerm(count, width))
				got := canonical(original)
				k := (count & mask(width)) % uint64(width)
				want := x
				if k != 0 {
					want = binaryTerm("or", binaryTerm("shr", x, constTerm(k, width)), binaryTerm("shl", x, constTerm(uint64(width)-k, width)))
				}
				if !equalTerms(got, want) {
					t.Fatalf("rotate spelling: got %s, want %s", got, want)
				}
				values := []uint64{0, 1, mask(width), uint64(1) << (width - 1), 0xAAAAAAAAAAAAAAAA, 0x5555555555555555}
				for range 64 {
					values = append(values, rng.Uint64())
				}
				for _, value := range values {
					env := map[string]uint64{"x": value & mask(width)}
					if got.eval(env) != original.eval(env) {
						t.Fatalf("x=%x: normalized=%x original=%x", value, got.eval(env), original.eval(env))
					}
				}
			})
		}
	}
	for _, width := range []int{8, 16, 32, 64} {
		x, n := paramTerm("x", width), paramTerm("n", width)
		original := binaryTerm("ror", x, n)
		if got := canonical(original); !equalTerms(got, original) {
			t.Fatalf("dynamic rotate changed: %s", got)
		}
		if width < 32 {
			original = binaryTerm("ror", x, constTerm(1, width))
			if got := canonical(original); !equalTerms(got, original) {
				t.Fatalf("unsupported rotate width changed: %s", got)
			}
		}
	}
}

func TestCanonicalBitwisePackedExtraction(t *testing.T) {
	for width := 2; width <= 6; width++ {
		for k := 1; k < width; k++ {
			for _, reverse := range []bool{false, true} {
				lo := binaryTerm("and", paramTerm("lo", width), constTerm(mask(k), width))
				hi := paramTerm("hi", width)
				shifted := binaryTerm("shl", hi, constTerm(uint64(k), width))
				packed := binaryTerm("or", lo, shifted)
				if reverse {
					packed = binaryTerm("or", shifted, lo)
				}
				original := binaryTerm("shr", packed, constTerm(uint64(k), width))
				got := canonical(original)
				want := binaryTerm("and", hi, constTerm(mask(width-k), width))
				if !equalTerms(got, want) {
					t.Fatalf("w%d k%d reversed=%v: got %s, want %s", width, k, reverse, got, want)
				}
				for l := uint64(0); l <= mask(width); l++ {
					for h := uint64(0); h <= mask(width); h++ {
						env := map[string]uint64{"lo": l, "hi": h}
						if got.eval(env) != original.eval(env) {
							t.Fatalf("w%d k%d lo=%x hi=%x", width, k, l, h)
						}
					}
				}
			}
		}
	}
	// Wide array leaves carry their narrow declared width. Extraction can
	// return the leaf directly only when the remaining bits contain it.
	for _, width := range []int{32, 64} {
		k := width / 2
		lo, hi := zeroExtend(paramTerm("lo", k), width), zeroExtend(paramTerm("hi", k), width)
		packed := binaryTerm("or", lo, binaryTerm("shl", hi, constTerm(uint64(k), width)))
		if got := canonical(binaryTerm("shr", packed, constTerm(uint64(k), width))); !equalTerms(got, hi) {
			t.Fatalf("narrow declared leaves must unpack exactly: %s", got)
		}
		wideHi := paramTerm("hi", width)
		original := binaryTerm("shr", binaryTerm("or", lo, binaryTerm("shl", wideHi, constTerm(uint64(k), width))), constTerm(uint64(k), width))
		got := canonical(original)
		for _, value := range []uint64{0, 1, mask(k), uint64(1) << k, mask(width)} {
			env := map[string]uint64{"lo": mask(k), "hi": value}
			if got.eval(env) != value&mask(k) || got.eval(env) != original.eval(env) {
				t.Fatalf("w%d wide high word was not masked: %s, hi=%x", width, got, value)
			}
		}
	}
}

func TestCanonicalBitwiseZeroShift(t *testing.T) {
	for _, width := range []int{8, 16, 32, 64} {
		for _, op := range []string{"shl", "shr", "sar"} {
			for _, count := range []uint64{0, uint64(width), uint64(width * 2)} {
				x := paramTerm("x", width)
				original := binaryTerm(op, x, constTerm(count, width))
				got := canonical(original)
				if !equalTerms(got, x) {
					t.Fatalf("w%d %s %d must be identity: %s", width, op, count, got)
				}
				for _, value := range []uint64{0, 1, mask(width), uint64(1) << (width - 1)} {
					env := map[string]uint64{"x": value}
					if got.eval(env) != original.eval(env) {
						t.Fatalf("w%d %s %d changed x=%x", width, op, count, value)
					}
				}
			}
		}
	}
}

func TestCanonicalBitwiseRefusesOtherShifts(t *testing.T) {
	for _, width := range []int{8, 16, 32, 64} {
		for _, op := range []string{"shl", "shr", "sar"} {
			x := paramTerm("x", width)
			for _, n := range []*term{constTerm(1, width), constTerm(uint64(width-1), width), constTerm(uint64(width+1), width), paramTerm("n", width)} {
				original := binaryTerm(op, x, n)
				if got := canonical(original); !equalTerms(got, original) {
					t.Fatalf("nonzero/dynamic shift changed: %s -> %s", original, got)
				}
			}
		}
	}
	// These are shape refusals only; a width outside the term evaluator's
	// supported domain must not be evaluated merely to test the guard.
	for _, op := range []string{"shl", "shr", "sar", "ror"} {
		for _, width := range []int{0, 65} {
			x, n := paramTerm("x", width), constTerm(0, width)
			original := binaryTerm(op, x, n)
			if got := canonicalBitwise(original, x, n); got != nil {
				t.Fatalf("unsupported width %d %s rewritten", width, op)
			}
		}
		x, n := paramTerm("x", 64), constTerm(0, 32)
		if got := canonicalBitwise(binaryTerm(op, x, n), x, n); got != nil {
			t.Fatalf("mismatched count width rewritten for %s", op)
		}
	}
}

func TestCanonicalBitwiseRepeatedMask(t *testing.T) {
	for _, width := range []int{4, 8, 32, 64} {
		for _, value := range []uint64{0, 1, mask(width / 2), 0xAAAAAAAAAAAAAAAA} {
			// Use a narrow computation as well as a full-width parameter:
			// the returned array's packing creates exactly this adapter.
			for _, x := range []*term{paramTerm("x", width), binaryTerm("xor", paramTerm("x", width/2), paramTerm("y", width/2))} {
				c := constTerm(value, width)
				inner := &term{kind: termBinary, op: "and", width: width, left: x, right: c}
				original := binaryTerm("and", inner, c)
				got := canonical(original)
				if !equalTerms(got, canonical(inner)) {
					t.Fatalf("repeated mask differs at w%d: %s", width, got)
				}
				for n := uint64(0); n < 256; n++ {
					env := map[string]uint64{"x": n & mask(x.width), "y": (^n) & mask(x.width)}
					if got.eval(env) != original.eval(env) {
						t.Fatalf("repeated mask changed at w%d, x=%x", width, n)
					}
				}
			}
		}
	}
	x := paramTerm("x", 64)
	inner := binaryTerm("and", x, constTerm(0xFF, 64))
	different := binaryTerm("and", inner, constTerm(0xF0, 64))
	if got := canonicalBitwise(different, inner, different.right); got != nil {
		t.Fatalf("different masks must not use idempotence: %s", got)
	}
}

func TestCanonicalBitwiseRefusesInexactExtraction(t *testing.T) {
	w := 64
	lo := binaryTerm("and", paramTerm("lo", w), constTerm(mask(32), w))
	hi, count := paramTerm("hi", w), constTerm(32, w)
	shifted := binaryTerm("shl", hi, count)
	for _, tc := range []struct {
		name               string
		lo, shifted, count *term
		op                 string
	}{
		{"overlapping low bits", paramTerm("lo", w), shifted, count, "shr"},
		{"different counts", lo, shifted, constTerm(31, w), "shr"},
		{"dynamic outer count", lo, shifted, paramTerm("n", w), "shr"},
		{"dynamic inner count", lo, binaryTerm("shl", hi, paramTerm("n", w)), count, "shr"},
		{"arithmetic shift", lo, shifted, count, "sar"},
		{"wrong inner operation", lo, binaryTerm("shr", hi, count), count, "shr"},
		{"narrow shifted operand", lo, binaryTerm("shl", paramTerm("hi", 32), constTerm(16, 32)), count, "shr"},
		{"narrow low operand", paramTerm("lo", 32), shifted, count, "shr"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			packed := &term{kind: termBinary, op: "or", width: w, left: tc.lo, right: tc.shifted}
			original := &term{kind: termBinary, op: tc.op, width: w, left: packed, right: tc.count}
			if got := canonicalBitwise(original, packed, tc.count); got != nil {
				t.Fatalf("inexact extraction must not rewrite: %s", got)
			}
		})
	}
	// A concrete bit at the first overlapping position refutes hi alone.
	original := binaryTerm("shr", binaryTerm("or", paramTerm("lo", w), shifted), count)
	env := map[string]uint64{"lo": uint64(1) << 32, "hi": 0}
	if canonical(original).eval(env) != 1 {
		t.Fatal("the overlapping low word was lost")
	}
	for _, k := range []uint64{0, 64} {
		original := binaryTerm("shr", binaryTerm("or", lo, binaryTerm("shl", hi, constTerm(k, w))), constTerm(k, w))
		env := map[string]uint64{"lo": 1, "hi": 2}
		if canonical(original).eval(env) != 3 {
			t.Fatalf("shift count %d must not discard the low operand", k)
		}
	}
}
