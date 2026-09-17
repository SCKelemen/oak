package prove

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/compiler"
)

// A theorem may name a package-level constant and may reason about `%`
// (docs/spec/125-verification.md). Both were open: an identifier that is
// not a parameter left the decider with nothing to fold, and unsigned
// division is an uninterpreted function of its operands, so a claim over
// a remainder falsified only the abstraction. The constants now reach the
// decider as the native backend's do, and division's defining bound —
// with a non-zero divisor the remainder is below it and the quotient is
// at most the dividend — is assumed, which is a fact and so cannot admit
// a false claim.
const theoremConstantsProgram = `
GAP: u32 = 4
CATALOG: u32 = 5

inset_len: (side: u32, gap: u32): u32 = side > gap * u32(2) ? side - gap * u32(2) | u32(0)

step: (c: u32, n: u32): u32 = n == u32(0) ? u32(0) | (c + u32(1)) % n

// Names a constant.
inset_fits: theorem (side: u32) { inset_len(side, GAP) <= side }

// Reasons about a remainder by a constant that is not a power of two.
cursor_in_range: theorem (c: u32) { step(c, CATALOG) < CATALOG }

// A power-of-two divisor folds to a mask and needed neither.
masked: theorem (x: u32) { x % u32(8) < u32(8) }

main: (): i32 = 0
`

// Both false: the assumed bound must not let them through.
const theoremConstantsRefutedProgram = `
too_tight: theorem (x: u32) { x % u32(5) < u32(4) }

is_identity: theorem (x: u32) { x % u32(5) == x }

main: (): i32 = 0
`

func proveSource(t *testing.T, src string) []Result {
	t.Helper()
	model, err := compiler.New().WithSource("thm.oak", src).SemanticModel().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	results, err := Theorems(model, 0)
	if err != nil {
		t.Fatalf("prove: %v", err)
	}
	return results
}

func TestTheoremsFoldConstantsAndBoundRemainders(t *testing.T) {
	byName := map[string]Result{}
	for _, r := range proveSource(t, theoremConstantsProgram) {
		byName[r.Name] = r
	}
	for _, name := range []string{"inset_fits", "cursor_in_range", "masked"} {
		got, found := byName[name]
		if !found {
			t.Fatalf("%s was not attempted; got %v", name, byName)
		}
		if got.Status != Decided {
			t.Errorf("%s must decide, got %s: %s", name, got.Status, got.Detail)
		}
	}
}

func TestTheoremsStillRefuteFalseRemainderClaims(t *testing.T) {
	for _, r := range proveSource(t, theoremConstantsRefutedProgram) {
		if r.Status != Refuted {
			t.Errorf("%s must be refuted, got %s: %s", r.Name, r.Status, r.Detail)
		}
		if !strings.Contains(r.Detail, "counterexample") {
			t.Errorf("%s must name a counterexample, got %q", r.Name, r.Detail)
		}
	}
}
