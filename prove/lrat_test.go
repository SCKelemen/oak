package prove

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
)

// The four clauses over a and b with every sign pattern are unsatisfiable;
// the certificate derives b from clauses 1 and 2, then the empty clause.
const lratFormula = "p cnf 2 4\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n"
const lratProof = "5 2 0 1 2 0\n5 d 1 2 0\n6 0 5 3 4 0\n"

func TestLRATAccepts(t *testing.T) {
	result, err := CheckLRAT(lratFormula, lratProof)
	if err != nil {
		t.Fatal(err)
	}
	if result.Additions != 2 || result.Deletions != 2 {
		t.Fatalf("counted %+v, want 2 additions and 2 deletions", result)
	}
}

func TestLRATRefuses(t *testing.T) {
	cases := map[string]struct{ proof, want string }{
		"no conflict":          {"5 2 0 1 0\n6 0 5 3 4 0\n", "reach no conflict"},
		"hint not unit":        {"5 0 1 0\n", "neither unit nor the conflict"},
		"dead hint":            {"5 2 0 1 2 0\n5 d 1 2 0\n6 0 5 1 2 0\n", "names no live clause"},
		"id does not increase": {"4 2 0 1 2 0\n", "does not increase"},
		"RAT hint refused":     {"5 2 0 -1 2 0\n", "RAT steps are not spoken"},
		"no empty clause":      {"5 2 0 1 2 0\n", "never derives the empty clause"},
		"undeclared variable":  {"5 3 0 1 2 0\n", "names no declared variable"},
		"satisfied hint":       {"5 -2 0 1 2 0\n", "already satisfied"},
		"malformed step":       {"5 2 1 2 0\n", "an addition is"},
	}
	for name, c := range cases {
		_, err := CheckLRAT(lratFormula, c.proof)
		if err == nil || !strings.Contains(err.Error(), c.want) {
			t.Errorf("%s: want an error mentioning %q, got %v", name, c.want, err)
		}
	}
	if _, err := CheckLRAT("p cnf 2 3\n1 2 0\n", lratProof); err == nil || !strings.Contains(err.Error(), "declares 3 clauses") {
		t.Errorf("clause count: got %v", err)
	}
}

// The clause engine agrees with the diagram engine: over every input of a
// small theorem the obligation clause is satisfiable exactly when the
// ladder refutes it (a trap or a false claim), and never when it decides.
func TestCNFAgreesWithBDD(t *testing.T) {
	src := `
double: (x: u8): u8 = x + x
rotl: (x: u8, n: u8): u8 = (x << (n & u8(7))) | (x >> ((u8(8) - n) & u8(7)))
rotr: (x: u8, n: u8): u8 = (x >> (n & u8(7))) | (x << ((u8(8) - n) & u8(7)))
shift_is_double: theorem (x: u8) { x << u8(1) == x + x }
mask_bound: theorem (x: u8, m: u8) { (x & m) <= m }
xor_cancel: theorem (a: u8, b: u8) { (a ^ b) ^ b == a }
overflow: theorem (x: u8) { x + u8(1) > x }
signed_wrap: theorem (x: i8) { x - x == i8(0) }
calls: theorem (x: u8) { double(x) == x * u8(2) }
rotations: theorem (x: u8, n: u8) { rotr(rotl(x, n), n) == x }
unmasked: theorem (x: u8, n: u8) { (x << n) >> n <= x }
mul_commutes: theorem (a: u8, b: u8) { a * b == b * a }
ite_pick: theorem (a: u8, b: u8) { (a > b ? a | b) >= a }
main: (): i32 = 0
`
	model := check(t, src)
	results, err := Theorems(model, 0)
	if err != nil {
		t.Fatal(err)
	}
	checked := 0
	for _, r := range results {
		if r.Status == Open {
			continue // the ladder had no verdict to agree with
		}
		cnf, reason, err := CNFFor(model, r.Name)
		if err != nil {
			t.Fatal(err)
		}
		if reason != "" {
			t.Fatalf("%s: %s", r.Name, reason)
		}
		if cnf.Settled != nil {
			// The clause engine's folding settled it: the constant must be
			// the ladder's verdict.
			proven := cnf.Settled.Kind == asm.DecisionProven
			if proven != (r.Status == Decided) {
				t.Errorf("%s: folded to %s, ladder %s", r.Name, cnf.Settled.Message, r.Status)
			}
			checked++
			continue
		}
		if cnf.InputBits() > 16 {
			t.Fatalf("%s: %d input bits is too many to enumerate", r.Name, cnf.InputBits())
		}
		params := map[string]uint64{}
		names := cnf.Names
		satisfiable := false
		total := uint64(1) << uint(cnf.InputBits())
		for assignment := uint64(0); assignment < total && !satisfiable; assignment++ {
			rest := assignment
			for _, name := range names {
				params[name] = rest & 0xFF
				rest >>= 8
			}
			satisfiable = cnf.Evaluate(params)
		}
		refuted := r.Status == Refuted
		if satisfiable != refuted {
			t.Errorf("%s: clauses satisfiable=%v, ladder %s (%s)", r.Name, satisfiable, r.Status, r.Detail)
		}
		if !strings.HasPrefix(cnf.Text, "c oak prove: "+r.Name+"\np cnf ") {
			t.Errorf("%s: DIMACS header %q", r.Name, cnf.Text[:40])
		}
		checked++
	}
	if checked < 9 {
		t.Fatalf("checked %d theorems, want at least 9", checked)
	}
}

// The word-protocol checker decides as the text checker does: the same
// acceptance with the same counts, the same refusals for every fixture the
// word form can express (a RAT hint, a malformed line, and an undeclared
// variable are refused by the encoder before any checker sees them).
func TestLRATWordsAgree(t *testing.T) {
	words, err := EncodeLRATWords(lratFormula, lratProof)
	if err != nil {
		t.Fatal(err)
	}
	fromWords, err := CheckLRATWords(words)
	if err != nil {
		t.Fatal(err)
	}
	fromText, _ := CheckLRAT(lratFormula, lratProof)
	if fromWords != fromText {
		t.Fatalf("words counted %+v, text %+v", fromWords, fromText)
	}
	cases := map[string]struct{ proof, want string }{
		"no conflict":          {"5 2 0 1 0\n6 0 5 3 4 0\n", "reach no conflict"},
		"hint not unit":        {"5 0 1 0\n", "neither unit nor the conflict"},
		"dead hint":            {"5 2 0 1 2 0\n5 d 1 2 0\n6 0 5 1 2 0\n", "names no live clause"},
		"id does not increase": {"4 2 0 1 2 0\n", "does not increase"},
		"no empty clause":      {"5 2 0 1 2 0\n", "never derives the empty clause"},
		"satisfied hint":       {"5 -2 0 1 2 0\n", "already satisfied"},
	}
	for name, c := range cases {
		words, err := EncodeLRATWords(lratFormula, c.proof)
		if err != nil {
			t.Fatalf("%s: encode: %v", name, err)
		}
		_, err = CheckLRATWords(words)
		if err == nil || !strings.Contains(err.Error(), c.want) {
			t.Errorf("%s: want an error mentioning %q, got %v", name, c.want, err)
		}
	}
	// A record whose steps run past its end, and one with an unknown kind.
	truncated := append([]uint32(nil), words[:len(words)-2]...)
	if _, err := CheckLRATWords(truncated); err == nil {
		t.Errorf("a truncated record must be refused")
	}
	unknown := append([]uint32(nil), words...)
	unknown[8+int(words[3])] = 2
	if _, err := CheckLRATWords(unknown); err == nil || !strings.Contains(err.Error(), "neither an addition") {
		t.Errorf("an unknown step kind must be refused, got %v", err)
	}
}
