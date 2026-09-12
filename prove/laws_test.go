package prove

import (
	"strings"
	"testing"
)

// Declared operator laws are theorems (docs/spec/10-syntax.md section 14a):
// over a record of Bool fields the ladder decides each exhaustively, and a
// false law is refuted with a counterexample rather than trusted.
func TestOperatorLawsAreDecided(t *testing.T) {
	src := `
Flag: type = struct { on: Bool }
flag_off: (): Flag = Flag { on: false }
operator(+) either: (a: Flag, b: Flag): Flag laws { associative, commutative, identity(flag_off()), idempotent } = Flag { on: a.on || b.on }
operator(*) differ: (a: Flag, b: Flag): Flag laws { commutative, idempotent } = Flag { on: a.on != b.on }
main: (): i32 = 0
`
	results, err := Theorems(check(t, src), 0)
	if err != nil {
		t.Fatal(err)
	}
	status := map[string]Result{}
	for _, r := range results {
		status[r.Name] = r
	}
	for _, name := range []string{"law_either_associative", "law_either_commutative", "law_either_identity_left", "law_either_identity_right", "law_either_idempotent", "law_differ_commutative"} {
		r, ok := status[name]
		if !ok || r.Status != Decided {
			t.Fatalf("%s: %+v", name, r)
		}
	}
	// differ is not idempotent: a != a is false, so differ(a, a) is off.
	if r := status["law_differ_idempotent"]; r.Status != Refuted || !strings.Contains(r.Detail, "counterexample") {
		t.Fatalf("law_differ_idempotent: %+v", r)
	}
	if fn, ok := IsLawObligation("law_either_identity_left"); !ok || fn != "either" {
		t.Fatalf("IsLawObligation = %q %v", fn, ok)
	}
}
