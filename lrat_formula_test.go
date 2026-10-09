package main

import (
	"context"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/SCKelemen/oak/compiler"
	"github.com/SCKelemen/oak/prove"
)

type formulaBindingCase struct {
	name            string
	formula, record []uint32
	want            bool
}

func formulaBindingCases(t *testing.T) []formulaBindingCase {
	t.Helper()
	encode := func(formula, proof string) []uint32 {
		words, err := prove.EncodeLRATWords(formula, proof)
		if err != nil {
			t.Fatal(err)
		}
		return words
	}
	formula := encode("p cnf 2 2\n1 0\n-1 0\n", "")
	record := encode("p cnf 2 2\n1 0\n-1 0\n", "3 0 1 2 0\n")
	cases := []formulaBindingCase{{"exact", formula, record, true}}
	for n := 0; n < len(record); n++ {
		cases = append(cases, formulaBindingCase{fmt.Sprintf("record truncated %d", n), formula, record[:n], false})
	}
	for n := 0; n < len(formula); n++ {
		cases = append(cases, formulaBindingCase{fmt.Sprintf("formula truncated %d", n), formula[:n], record, false})
	}
	mutate := func(name string, targetFormula bool, index int, value uint32, want bool) {
		f, r := append([]uint32(nil), formula...), append([]uint32(nil), record...)
		if targetFormula {
			f[index] = value
		} else {
			r[index] = value
		}
		cases = append(cases, formulaBindingCase{name, f, r, want})
	}
	for _, isFormula := range []bool{false, true} {
		for _, index := range []int{0, 1, 2, 3, 4, 8, 9, 10, 11} {
			mutate(fmt.Sprintf("mutate formula=%t field=%d", isFormula, index), isFormula, index, ^uint32(0), false)
		}
		for _, index := range []int{5, 6, 7} {
			mutate(fmt.Sprintf("capacity formula=%t field=%d", isFormula, index), isFormula, index, 123, true)
		}
	}
	cases = append(cases,
		formulaBindingCase{"record trailing words", formula, append(append([]uint32(nil), record...), 0), false},
		formulaBindingCase{"formula trailing words", append(append([]uint32(nil), formula...), 0), record, false},
		formulaBindingCase{"same dimensions different UNSAT formula", formula, encode("p cnf 2 2\n2 0\n-2 0\n", "3 0 1 2 0\n"), false},
		formulaBindingCase{"same dimensions SAT formula", encode("p cnf 2 2\n1 0\n1 0\n", ""), record, false},
		formulaBindingCase{"clause order", encode("p cnf 2 2\n-1 0\n1 0\n", ""), record, false},
		formulaBindingCase{"initial empty clause", encode("p cnf 0 1\n0\n", ""), encode("p cnf 0 1\n0\n", ""), true},
		formulaBindingCase{"empty formula identity is not a proof", encode("p cnf 0 0\n", ""), encode("p cnf 0 0\n", ""), true},
	)
	// Same Boolean meaning still does not preserve exact hint numbering/text.
	for _, pair := range [][2]string{
		{"p cnf 2 2\n1 2 0\n0\n", "p cnf 2 2\n2 1 0\n0\n"},
		{"p cnf 2 2\n1 1 2 0\n0\n", "p cnf 2 2\n1 2 2 0\n0\n"},
	} {
		cases = append(cases, formulaBindingCase{"literal order/multiplicity", encode(pair[0], ""), encode(pair[1], ""), false})
	}
	// Identity may succeed on malformed clause syntax. Whole-record soundness
	// must derive decoder locality from the checker, not identity alone.
	for _, mutation := range []struct {
		name  string
		index int
		value uint32
	}{
		{"matching oversized initial length", 8, ^uint32(0)},
		{"matching invalid literal", 9, 4},
		{"matching zero length with trailing payload", 8, 0},
	} {
		f, r := append([]uint32(nil), formula...), append([]uint32(nil), record...)
		f[mutation.index], r[mutation.index] = mutation.value, mutation.value
		cases = append(cases, formulaBindingCase{mutation.name, f, r, true})
	}
	return cases
}

func TestLRATFormulaBinding(t *testing.T) {
	for _, c := range formulaBindingCases(t) {
		t.Run(c.name, func(t *testing.T) {
			if got := prove.LRATWordsMatchFormula(c.formula, c.record); got != c.want {
				t.Fatalf("binding = %t, want %t", got, c.want)
			}
		})
	}
	unsat := "p cnf 2 2\n1 0\n-1 0\n"
	record, err := prove.EncodeLRATWords(unsat, "3 0 1 2 0\n")
	if err != nil {
		t.Fatal(err)
	}
	if result, err := prove.CheckLRATWordsAgainst(unsat, record); err != nil || result.Additions != 1 {
		t.Fatalf("valid bound proof: %+v %v", result, err)
	}
	for _, other := range []string{"p cnf 2 2\n1 0\n1 0\n", "p cnf 2 2\n2 0\n-2 0\n", "invalid"} {
		if _, err := prove.CheckLRATWordsAgainst(other, record); err == nil {
			t.Fatalf("accepted substituted formula %q", other)
		}
	}
	badProof := append([]uint32(nil), record...)
	badProof[len(badProof)-1] = 1 // two positive units never reach conflict
	if !prove.LRATWordsMatchFormula(formulaBindingCases(t)[0].formula, badProof) {
		t.Fatal("proof mutation unexpectedly changes formula identity")
	}
	if _, err := prove.CheckLRATWordsAgainst(unsat, badProof); err == nil {
		t.Fatal("identity alone accepted an invalid proof")
	}
}

// Execute the production Oak predicate on the same raw words as the Go gate.
// This deliberately bypasses the Go encoder's admission checks for corrupt
// cases, including all truncations and wrapping u32 lengths.
func TestOakLRATFormulaBinding(t *testing.T) {
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Skip("no C compiler for the bootstrap differential")
	}
	var source strings.Builder
	source.WriteString("package main\n")
	source.WriteString("malloc: (n: c.Size): c.Ptr = c.extern(\"malloc\")\nfree: (p: c.Ptr): () = c.extern(\"free\")\n")
	source.WriteString(oakLRATSource)
	// Include the production acceptance wrapper, rather than a test copy.
	start := strings.Index(oakCertifySource, "lrat_check_record:")
	end := strings.Index(oakCertifySource, "// write_words_file")
	if start < 0 || end <= start {
		t.Fatal("cannot locate the production record acceptance wrapper")
	}
	source.WriteString(oakCertifySource[start:end])
	source.WriteString("\nmain: (): i32 {\n")
	cases := formulaBindingCases(t)
	for _, c := range cases {
		source.WriteString("true ? {\n")
		for i, words := range [][]uint32{c.formula, c.record} {
			fmt.Fprintf(&source, "w%d: [%d]u32\n", i, max(1, len(words)))
			for j, word := range words {
				fmt.Fprintf(&source, "w%d[u32(%d)] = u32(%d)\n", i, j, word)
			}
			fmt.Fprintf(&source, "all%d: []u32 = view(&w%d)\nv%d: []u32 = subslice(all%d, u32(0), u32(%d))\n", i, i, i, i, len(words))
		}
		fmt.Fprintf(&source, "assert(lrat_matches_formula(v0, v1) == %t)\n", c.want)
		source.WriteString("checked: [3]u32\nchecked[u32(0)] = u32(99)\nchecked[u32(1)] = u32(99)\nchecked[u32(2)] = u32(99)\n")
		source.WriteString("status: u32 = lrat_check_record(v0, v1, span(&checked))\nassert(status == checked[u32(0)])\n")
		if !c.want {
			source.WriteString("assert(status == LRAT_FORMULA_MISMATCH)\nassert(checked[u32(1)] == u32(0) && checked[u32(2)] == u32(0))\n")
		} else {
			_, err := prove.CheckLRATWords(c.record)
			fmt.Fprintf(&source, "assert((status == LRAT_ACCEPTED) == %t)\n", err == nil)
		}
		source.WriteString("}\n")
	}
	source.WriteString("0\n}\n")
	generated, err := compiler.New().WithSource("formula_binding.oak", source.String()).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	dir := t.TempDir()
	cpath, bin := filepath.Join(dir, "binding.c"), filepath.Join(dir, "binding")
	if err := os.WriteFile(cpath, []byte(generated), 0600); err != nil {
		t.Fatal(err)
	}
	if out, err := exec.Command(cc, "-std=c99", "-O1", "-o", bin, cpath).CombinedOutput(); err != nil {
		t.Fatalf("cc: %v\n%s", err, out)
	}
	if out, err := exec.Command(bin).CombinedOutput(); err != nil {
		t.Fatalf("Oak binding: %v\n%s", err, out)
	}
	t.Logf("production Oak binding agreed on %d raw-record cases", len(cases))
}

// The formal CI lane requires this oracle. Ordinary Go-only environments
// still run the production Go/Oak tests above without claiming Lean replay.
func TestLRATFormulaBindingMatchesLean(t *testing.T) {
	lake, err := exec.LookPath("lake")
	if err != nil {
		if os.Getenv("OAK_REQUIRE_LRAT_BINDING_LEAN") != "" {
			t.Fatal("lake is required for the formula-binding correspondence gate")
		}
		t.Skip("lake not on PATH; formal CI requires the Lean replay")
	}
	var source strings.Builder
	source.WriteString("import Oak.LRATBoundSoundness\nimport Oak.LRATBindingExtracted\n\n")
	list := func(words []uint32) string {
		items := make([]string, len(words))
		for i, word := range words {
			items[i] = fmt.Sprint(word)
		}
		return "[" + strings.Join(items, ", ") + "]"
	}
	for _, c := range formulaBindingCases(t) {
		got := prove.LRATWordsMatchFormula(c.formula, c.record)
		if got != c.want {
			t.Fatalf("%s: production binding %t, want %t", c.name, got, c.want)
		}
		fmt.Fprintf(&source, "example : Oak.LRATFormulaBinding.matchesFormula %s %s = %t := by decide\n", list(c.formula), list(c.record), got)
		fmt.Fprintf(&source, "example : Oak.LRATBinding.lrat_matches_formula #%s #%s %d = some %t := by decide\n", list(c.formula), list(c.record), len(c.formula)+1, got)
	}
	source.WriteString(`
open Oak.LRATFormulaBinding in
example (formula record starts lengths : Array UInt32)
    (alive : Array UInt8) (store : Array UInt32) (assign : Array UInt8) (trail out : Array UInt32)
    (fuel : Nat) (s l : Array UInt32) (v : Array UInt8) (t : Array UInt32)
    (x : Array UInt8) (y o : Array UInt32) (clauses : List Oak.RupCheck.Clause)
    (bound : matchesFormula (project formula) (project record) = true)
    (decoded : decodeInitial formula 8 (8 + (formula.getD 3 0).toNat)
      (formula.getD 2 0).toNat = some clauses)
    (run : Oak.LRATChecker.lrat_check record starts lengths alive store assign trail out fuel =
      some (Oak.LRATChecker.LRAT_ACCEPTED, s, l, v, t, x, y, o)) :
    ¬ ∃ a, ∀ clause ∈ clauses, Oak.RupCheck.SatisfiesClause a clause :=
  production_bound_record_sound formula record starts lengths alive store assign trail out
    fuel s l v t x y o clauses bound decoded run
example : Oak.LRATFormulaBinding.decodeInitial #[1, 0, 1, 1] 0 4 2 =
    some [Oak.LRATChecker.inputClause #[1, 0, 1, 1] 1 1,
      Oak.LRATChecker.inputClause #[1, 0, 1, 1] 3 1] := by decide
example : Oak.LRATFormulaBinding.decodeInitial #[] 0 0 0 = some [] := by decide
example : Oak.LRATFormulaBinding.decodeInitial #[0] 0 1 1 = some [[]] := by decide
example : Oak.LRATFormulaBinding.decodeInitial #[] 0 1 1 = none := by decide
example : Oak.LRATFormulaBinding.decodeInitial #[] 1 1 0 = none := by decide
example : Oak.LRATFormulaBinding.decodeInitial #[1] 0 1 1 = none := by decide
example : Oak.LRATFormulaBinding.decodeInitial #[4294967295] 0 1 1 = none := by decide
example : Oak.LRATFormulaBinding.decodeInitial #[0, 0] 0 2 1 = none := by decide
example : Oak.LRATFormulaBinding.decodeInitial #[0] 0 1 2 = none := by decide
#print axioms Oak.LRATFormulaBinding.production_bound_record_sound
#print axioms Oak.LRATFormulaBinding.decodeInitial_transfer
`)
	path := filepath.Join(t.TempDir(), "FormulaBindingPins.lean")
	if err := os.WriteFile(path, []byte(source.String()), 0600); err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(context.Background(), 3*time.Minute)
	defer cancel()
	for _, args := range [][]string{{"build", "Oak.LRATBoundSoundness", "Oak.LRATBindingExtracted"}, {"env", "lean", path}} {
		cmd := exec.CommandContext(ctx, lake, args...)
		cmd.Dir = filepath.Join("spec", "lean")
		out, err := cmd.CombinedOutput()
		if err != nil {
			t.Fatalf("Lean formula binding: %v (%v)\n%s", err, ctx.Err(), out)
		}
		if strings.Contains(string(out), "sorryAx") {
			t.Fatalf("formula-binding soundness depends on a proof hole:\n%s", out)
		}
	}
}
