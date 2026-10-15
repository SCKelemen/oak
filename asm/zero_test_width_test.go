package asm

import (
	"fmt"
	"testing"
)

func TestZeroTestOfRequiresBooleanNonzero(t *testing.T) {
	for _, width := range []int{1, 2, 8, 32, 64} {
		for _, op := range []string{"eq", "ne"} {
			t.Run(fmt.Sprintf("%s_width_%d", op, width), func(t *testing.T) {
				x := paramTerm("x", width)
				fact := truncate(cmpTerm(op, x, constTerm(0, width)), 1)
				value := canonical(truncate(x, 1))
				want := 0
				if op == "eq" {
					want = 1
				} else if width == 1 {
					want = -1
				}
				got := zeroTestOf(fact, value, newCanonicalTable(), map[*term]bool{})
				if got != want {
					t.Fatalf("zero test relation = %d, want %d", got, want)
				}
				for raw := uint64(0); raw < 256; raw++ {
					env := map[string]uint64{"x": raw}
					if fact.eval(env)&1 == 0 || got == 0 {
						continue
					}
					if bit := value.eval(env) & 1; (got == 1 && bit != 0) || (got == -1 && bit != 1) {
						t.Fatalf("invalid relation %d at x=%d, bit=%d", got, raw, bit)
					}
				}
			})
		}
	}
	// A wider term whose range really is {0,1} retains the useful rule.
	for name, value := range map[string]*term{
		"comparison":  cmpTerm("eq", paramTerm("x", 8), constTerm(2, 8)),
		"Boolean_ite": iteTerm(paramTerm("bit", 1), constTerm(1, 8), constTerm(0, 8)),
		"masked_bit":  binaryTerm("and", paramTerm("x", 8), constTerm(1, 8)),
	} {
		t.Run(name, func(t *testing.T) {
			fact := truncate(cmpTerm("ne", value, constTerm(0, value.width)), 1)
			if got := zeroTestOf(fact, canonical(truncate(value, 1)), newCanonicalTable(), map[*term]bool{}); got != -1 {
				t.Fatalf("Boolean range at width %d lost: relation=%d", value.width, got)
			}
		})
	}
	// A widened parameter keeps declared width metadata, but the existing
	// range recognizer does not use that metadata. Conservative refusal is safe.
	extended := zeroExtend(paramTerm("bit", 1), 8)
	fact := truncate(cmpTerm("ne", extended, constTerm(0, 8)), 1)
	if got := zeroTestOf(fact, canonical(truncate(extended, 1)), newCanonicalTable(), map[*term]bool{}); got != 0 {
		t.Fatalf("unrecognized wide parameter range must remain unknown: %d", got)
	}
}

func TestPruneUnderDirectNonzeroPreservesLowBit(t *testing.T) {
	for _, width := range []int{2, 8, 32, 64} {
		t.Run(fmt.Sprintf("width_%d", width), func(t *testing.T) {
			x := paramTerm("x", width)
			low := truncate(x, 1)
			for _, op := range []string{"eq", "ne"} {
				// A single direct comparison, with no OR/common-fact rule.
				premise := truncate(cmpTerm(op, x, constTerm(0, width)), 1)
				original := []*term{x, low, cmpTerm("eq", x, constTerm(0, width)), iteTerm(low, constTerm(7, 8), constTerm(9, 8))}
				before := premise.String()
				got := pruneUnderFacts(premise, original)
				for raw := uint64(0); raw < 256; raw++ {
					env := map[string]uint64{"x": raw}
					if premise.eval(env)&1 == 0 {
						continue
					}
					for i, term := range original {
						if got[i].width != term.width || got[i].eval(env) != term.eval(env) {
							t.Fatalf("%s x=%d: term %d changed from %s (width %d, value %d) to %s (width %d, value %d)", op, raw, i, term, term.width, term.eval(env), got[i], got[i].width, got[i].eval(env))
						}
					}
				}
				if premise.String() != before {
					t.Fatal("premise was mutated")
				}
			}
		})
	}
}

func TestImpliesEqualRefutesNonzeroLowBit(t *testing.T) {
	x := paramTerm("x", 8)
	low := truncate(x, 1)
	nonzero := truncate(cmpTerm("ne", x, constTerm(0, 8)), 1)
	one := constTerm(1, 1)
	model := map[string]uint64{"x": 2}
	if nonzero.eval(model) != 1 || low.eval(model) == one.eval(model) {
		t.Fatal("expected concrete counterexample x=2")
	}
	// The actual implication caller runs fact pruning before valuation checks.
	// It must refute this false equality even without the OR collector.
	widthOf := func(string) int { return 8 }
	session := &verificationSession{}
	if holds, decided := session.impliesEqual(nonzero, low, one, widthOf); holds || !decided {
		t.Fatalf("nonzero does not establish parity: holds=%v decided=%v", holds, decided)
	}
	zero := truncate(cmpTerm("eq", x, constTerm(0, 8)), 1)
	if holds, decided := session.impliesEqual(zero, low, constTerm(0, 1), widthOf); !holds || !decided {
		t.Fatalf("zero must establish a clear low bit: holds=%v decided=%v", holds, decided)
	}
	bit := paramTerm("bit", 1)
	if holds, decided := session.impliesEqual(cmpTerm("ne", bit, constTerm(0, 1)), bit, one, func(string) int { return 1 }); !holds || !decided {
		t.Fatalf("one-bit nonzero rule lost: holds=%v decided=%v", holds, decided)
	}
}
