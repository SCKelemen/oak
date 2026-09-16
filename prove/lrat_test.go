package prove

import (
	"fmt"
	"slices"
	"strconv"
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
		"no conflict":     {"5 2 0 1 0\n6 0 5 3 4 0\n", "reach no conflict"},
		"hint not unit":   {"5 0 1 0\n", "neither unit nor the conflict"},
		"no empty clause": {"5 2 0 1 2 0\n", "never derives the empty clause"},
		"satisfied hint":  {"5 -2 0 1 2 0\n", "already satisfied"},
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

func TestEncodeLRATWordsStable(t *testing.T) {
	want := []uint32{
		LRATMagic, 2, 4, 12, 19, 6, 9, 0,
		2, 1, 3,
		2, 0, 3,
		2, 1, 2,
		2, 0, 2,
		0, 5, 1, 3, 2, 1, 2,
		1, 5, 2, 1, 2,
		0, 6, 0, 3, 5, 3, 4,
	}
	got, err := EncodeLRATWords(lratFormula, lratProof)
	if err != nil {
		t.Fatal(err)
	}
	if !slices.Equal(got, want) {
		t.Fatalf("encoded words\n got %v\nwant %v", got, want)
	}
}

func TestEncodeLRATWordsRemapsSparseClauseIDs(t *testing.T) {
	if strconv.IntSize != 64 {
		t.Skip("sparse source id exceeds a 32-bit host int")
	}
	const sparse = uint64(1 << 40)
	formula := "p cnf 1 2\n1 0\n-1 0\n"
	proof := fmt.Sprintf("%d 1 0 1 0\n%d d %d 0\n%d 0 1 2 0\n", sparse, sparse, sparse, sparse+1)
	words, err := EncodeLRATWords(formula, proof)
	if err != nil {
		t.Fatal(err)
	}
	want := []uint32{
		LRATMagic, 1, 2, 4, 16, 4, 3, 0,
		1, 1,
		1, 0,
		0, 3, 1, 1, 1, 1,
		1, 3, 1, 3,
		0, 4, 0, 2, 1, 2,
	}
	if !slices.Equal(words, want) {
		t.Fatalf("encoded sparse IDs\n got %v\nwant %v", words, want)
	}
	if _, err := CheckLRATWords(words); err != nil {
		t.Fatalf("dense replay: %v", err)
	}
}

func TestEncodeLRATWordsRefusesInvalidReferences(t *testing.T) {
	formula := "p cnf 1 2\n1 0\n-1 0\n"
	cases := map[string]string{
		"absent hint":        "3 0 9 0\n",
		"future hint":        "3 0 4 0\n",
		"absent deletion":    "2 d 9 0\n",
		"duplicate deletion": "3 1 0 1 0\n3 d 3 3 0\n",
		"deleted hint":       "3 1 0 1 0\n3 d 3 0\n4 0 3 2 0\n",
		"addition ordering":  "3 1 0 1 0\n3 0 1 2 0\n",
		"deletion ordering":  "3 1 0 1 0\n2 d 1 0\n",
	}
	for name, proof := range cases {
		if _, err := EncodeLRATWords(formula, proof); err == nil {
			t.Errorf("%s: encoded an invalid clause reference", name)
		}
	}
}

func TestEncodeLRATWordsRejectsMinInt(t *testing.T) {
	minInt := -int(^uint(0)>>1) - 1
	proof := fmt.Sprintf("1 %d 0 0\n", minInt)
	if _, err := EncodeLRATWords("p cnf 1 0\n", proof); err == nil {
		t.Fatal("encoded MinInt as a certificate literal")
	}
}

func TestEncodeLRATWordsRepresentability(t *testing.T) {
	max := maxLRATWord
	if got, err := lratUint32("test count", max); err != nil || uint64(got) != max {
		t.Fatalf("maximum word: got %d, %v", got, err)
	}
	if _, err := lratUint32("test count", max+1); err == nil {
		t.Fatal("accepted a count larger than uint32")
	}
	if got, err := lratAdd("test aggregate", max-1, 1); err != nil || got != max {
		t.Fatalf("maximum aggregate: got %d, %v", got, err)
	}
	if _, err := lratAdd("test aggregate", max, 1); err == nil {
		t.Fatal("accepted an overflowing aggregate")
	}
	if _, err := lratAdd("test aggregate", max+1, 0); err == nil {
		t.Fatal("accepted an already overflowing aggregate")
	}

	if strconv.IntSize != 64 {
		return
	}
	const maxUint32 = uint64(1<<32 - 1)
	const tooLarge = uint64(1 << 32)
	words, err := EncodeLRATWords(fmt.Sprintf("p cnf %d 1\n0\n", maxUint32), "")
	if err != nil {
		t.Fatalf("maximum variable header: %v", err)
	}
	if words[1] != ^uint32(0) {
		t.Fatalf("variable header %d, want uint32 max", words[1])
	}

	words, err = EncodeLRATWords(fmt.Sprintf("p cnf %d 1\n%d 0\n", maxLRATLiteralVariable, maxLRATLiteralVariable), "")
	if err != nil {
		t.Fatalf("maximum literal: %v", err)
	}
	if words[9] != ^uint32(0) {
		t.Fatalf("literal word %d, want uint32 max", words[9])
	}

	cases := map[string]struct {
		formula string
		proof   string
	}{
		"variable count": {fmt.Sprintf("p cnf %d 0\n", tooLarge), ""},
		"literal":        {fmt.Sprintf("p cnf %d 1\n%d 0\n", maxUint32, maxLRATLiteralVariable+1), ""},
	}
	for name, test := range cases {
		if _, err := EncodeLRATWords(test.formula, test.proof); err == nil {
			t.Errorf("%s: encoded a value outside the word protocol", name)
		}
	}
}
