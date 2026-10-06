package main

import (
	"bytes"
	"context"
	"fmt"
	"math/rand"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/compiler"
	"github.com/SCKelemen/oak/prove"
)

// Replace only the untrusted solver in a separately cached test binary. The
// production drivers and model checker must refuse its false SAT report.
func TestOakSATModelRejectsCorruptSolver(t *testing.T) {
	t.Setenv("OAK_SOLVER_NATIVE", "")
	original := oakSATSource
	start := strings.Index(original, "\nsat_solve:")
	if start < 0 {
		t.Fatal("cannot locate solver entry point")
	}
	oakSATSource = original[:start] + `
sat_solve: (l: SatLayout, mem: [*]u32): u32 {
  v: u32 = 0
  while v < l.vars {
    mem[l.assign_at + v] = u32(1)
    v = v + u32(1)
  }
  SAT_SATISFIABLE
}
`
	t.Cleanup(func() { oakSATSource = original })
	outcome, err := runOakSAT(cnfOf(1, [][]int{{1}}))
	if err == nil || outcome.Satisfiable || !strings.Contains(err.Error(), "s UNKNOWN 4") {
		t.Fatalf("SAT driver reported a fabricated model: %+v, %v", outcome, err)
	}
	model, err := compiler.New().WithSource("claim.oak", "claim: theorem (x: u32) { x == u32(0) }\nmain: (): i32 = 0\n").SemanticModel().Get()
	if err != nil {
		t.Fatal(err)
	}
	problem, reason, err := prove.ProblemFor(model, "claim", "interleaved", asm.NodeBudget)
	if err != nil || reason != "" {
		t.Fatalf("problem lowering: %s, %v", reason, err)
	}
	run, err := runOakClauses(problem)
	if err == nil || run.Constant != 0 || run.Outcome.Satisfiable || !strings.Contains(err.Error(), "s UNKNOWN 4") {
		t.Fatalf("CNF driver reported a fabricated model: %+v, %v", run, err)
	}
	// The self-hosted shell checks the same original formula before using a
	// SAT answer to contradict its diagram result. No Go cross-check runs.
	var out, errOut bytes.Buffer
	code := proveCommand([]string{"-solver", "self", "-cross", "none", filepath.Join("spec", "oak", "machines.oak")}, &out, &errOut)
	if code != 0 || strings.Contains(out.String(), "disagrees") || !strings.Contains(out.String(), "oak prove: 15 decided") {
		t.Fatalf("self-hosted shell trusted fabricated SAT evidence: exit %d\n%s%s", code, out.String(), errOut.String())
	}
}

type satModelCase struct {
	name                string
	formula, assignment []uint32
	want                bool
}

func satModelCases(t *testing.T) []satModelCase {
	t.Helper()
	encode := func(text string) []uint32 {
		words, err := prove.EncodeLRATWords(text, "")
		if err != nil {
			t.Fatal(err)
		}
		return words
	}
	var cases []satModelCase
	// Exhaust every clause of length 0..3 over two variables, including
	// duplicates and tautologies, under every complete assignment. The
	// oracle evaluates signed DIMACS literals, not the Oak word scan.
	for n, count := 0, 1; n <= 3; n, count = n+1, count*4 {
		for code := 0; code < count; code++ {
			clause, rest := make([]int, n), code
			for i := range clause {
				clause[i], rest = []int{-2, -1, 1, 2}[rest%4], rest/4
			}
			cnf := cnfOf(2, [][]int{clause})
			for bits := 0; bits < 4; bits++ {
				assignment, model := make([]uint32, 2), make([]int, 2)
				for v := range assignment {
					assignment[v], model[v] = 1, -(v + 1)
					if bits>>v&1 != 0 {
						assignment[v], model[v] = 2, v+1
					}
				}
				want, err := prove.ModelSatisfies(cnf.Text, model)
				if err != nil {
					t.Fatal(err)
				}
				cases = append(cases, satModelCase{fmt.Sprintf("clause/%v/model/%d", clause, bits), encode(cnf.Text), assignment, want})
			}
		}
	}
	rng := rand.New(rand.NewSource(20261006))
	for i := 0; i < 128; i++ {
		clauses := make([][]int, 1+rng.Intn(8))
		for j := range clauses {
			for n := rng.Intn(5); n > 0; n-- {
				clauses[j] = append(clauses[j], []int{-3, -2, -1, 1, 2, 3}[rng.Intn(6)])
			}
		}
		assignment, model := make([]uint32, 3), make([]int, 3)
		for v := range assignment {
			assignment[v], model[v] = 1, -(v + 1)
			if rng.Intn(2) != 0 {
				assignment[v], model[v] = 2, v+1
			}
		}
		cnf := cnfOf(3, clauses)
		want, err := prove.ModelSatisfies(cnf.Text, model)
		if err != nil {
			t.Fatal(err)
		}
		cases = append(cases, satModelCase{fmt.Sprintf("formula/%d", i), encode(cnf.Text), assignment, want})
	}
	valid := encode("p cnf 2 2\n1 2 0\n-2 0\n")
	assignment := []uint32{2, 1}
	cases = append(cases,
		satModelCase{"empty formula", encode("p cnf 0 0\n"), nil, true},
		satModelCase{"unused variable", encode("p cnf 1 0\n"), []uint32{1}, true},
		satModelCase{"unused invalid variable", encode("p cnf 1 0\n"), []uint32{3}, false},
		satModelCase{"empty clause", encode("p cnf 0 1\n0\n"), nil, false},
		satModelCase{"trailing word", append(append([]uint32(nil), valid...), 0), assignment, false},
		satModelCase{"short assignment", valid, assignment[:1], false},
		satModelCase{"long assignment", valid, []uint32{2, 1, 1}, false},
	)
	for n := 0; n < len(valid); n++ {
		cases = append(cases, satModelCase{fmt.Sprintf("truncated/%d", n), valid[:n], assignment, false})
	}
	for _, field := range []int{0, 1, 2, 3, 4, 8, 10, 11, 12} {
		for _, value := range []uint32{0xfffffffc, 0xffffffff} {
			words := append([]uint32(nil), valid...)
			words[field] = value
			cases = append(cases, satModelCase{fmt.Sprintf("malformed/%d/%x", field, value), words, assignment, false})
		}
	}
	for _, value := range []uint32{0, 3, 0xffffffff} {
		cases = append(cases, satModelCase{fmt.Sprintf("invalid assignment/%d", value), valid, []uint32{2, value}, false})
	}
	for _, field := range []int{2, 3} {
		words := append([]uint32(nil), valid...)
		words[field]--
		cases = append(cases, satModelCase{fmt.Sprintf("underdeclared/%d", field), words, assignment, false})
	}
	for _, field := range []int{5, 6, 7} {
		words := append([]uint32(nil), valid...)
		words[field] = 0xffffffff
		cases = append(cases, satModelCase{fmt.Sprintf("capacity hint/%d", field), words, assignment, true})
	}
	return cases
}

// Extract the complete read-only checker, including its loops. Drift is a
// failure; bounded kernel replay below uses this exact committed extraction.
func TestOakSATModelExtraction(t *testing.T) {
	source := oakLRATSource + "\n" + oakModelSource
	extracted, err := compiler.New().WithSource("model.oak", source).EmitLeanRoots("Oak.SATModel", []string{"sat_check_model"}).Get()
	if err != nil {
		t.Fatal(err)
	}
	if strings.Contains(extracted, "sorry") {
		t.Fatal("SAT-model extraction contains sorry")
	}
	path := filepath.Join("spec", "lean", "Oak", "SATModelExtracted.lean")
	if os.Getenv("OAK_LEAN_EXTRACT_UPDATE") == "1" {
		if err := os.WriteFile(path, []byte(extracted), 0644); err != nil {
			t.Fatal(err)
		}
	}
	committed, err := os.ReadFile(path)
	if err != nil || string(committed) != extracted {
		t.Fatalf("SAT-model extraction drift (%v); regenerate with OAK_LEAN_EXTRACT_UPDATE=1", err)
	}
}

func TestOakSATModelRawWords(t *testing.T) {
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Fatal("C compiler required for the production SAT-model checker")
	}
	cases := satModelCases(t)
	var data, starts, sizes, models, modelStarts, modelSizes []uint32
	for _, c := range cases {
		starts, sizes = append(starts, uint32(len(data))), append(sizes, uint32(len(c.formula)))
		modelStarts, modelSizes = append(modelStarts, uint32(len(models))), append(modelSizes, uint32(len(c.assignment)))
		data, models = append(data, c.formula...), append(models, c.assignment...)
	}
	list := func(words []uint32) string {
		items := make([]string, len(words))
		for i, word := range words {
			items[i] = fmt.Sprint(word)
		}
		return strings.Join(items, ", ")
	}
	var source strings.Builder
	source.WriteString("import(std)\nputchar: (ch: c.Int): c.Int = c.extern(\"putchar\")\n" + oakLRATSource + "\n" + oakModelSource + "\nmain: (): i32 {\n")
	for i, words := range [][]uint32{data, starts, sizes, models, modelStarts, modelSizes} {
		fmt.Fprintf(&source, "w%d: [%d]u32 = [%d]u32{%s}\n", i, len(words), len(words), list(words))
	}
	source.WriteString(`
  all: []u32 = view(&w0)
  models: []u32 = view(&w3)
  i: u32 = 0
  while i < len(w1) {
    formula: []u32 = subslice(all, w1[i], w2[i])
    assignment: []u32 = subslice(models, w4[i], w5[i])
    accepted: Bool = sat_check_model(formula, assignment)
    _ = putchar(accepted ? { c.Int(49) } | { c.Int(48) })
    i = i + u32(1)
  }
  0
}
`)
	generated, err := compiler.New().WithSource("model_test.oak", source.String()).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	dir := t.TempDir()
	cpath, bin := filepath.Join(dir, "model.c"), filepath.Join(dir, "model")
	if err := os.WriteFile(cpath, []byte(generated), 0600); err != nil {
		t.Fatal(err)
	}
	if out, err := exec.Command(cc, "-std=c99", "-O1", "-o", bin, cpath).CombinedOutput(); err != nil {
		t.Fatalf("cc: %v\n%s", err, out)
	}
	output, err := exec.Command(bin).Output()
	if err != nil || len(output) != len(cases) {
		t.Fatalf("Oak model checker: %v, got %d/%d results", err, len(output), len(cases))
	}
	for i, c := range cases {
		if output[i] != '0' && output[i] != '1' || (output[i] == '1') != c.want {
			t.Errorf("%s: Oak returned %q, want %t", c.name, output[i], c.want)
		}
	}
	t.Logf("checked %d raw formula/model pairs", len(cases))
	t.Run("Lean", func(t *testing.T) {
		lake, err := exec.LookPath("lake")
		if err != nil {
			if os.Getenv("OAK_REQUIRE_SAT_MODEL_LEAN") != "" {
				t.Fatal("lake is required for the SAT-model correspondence gate")
			}
			t.Skip("lake not on PATH; formal CI requires the extracted-checker replay")
		}
		var pins strings.Builder
		pins.WriteString("import Oak.SATModel\nset_option maxRecDepth 65536\nset_option maxHeartbeats 4000000\n")
		for i, c := range cases {
			fmt.Fprintf(&pins, "example : Oak.SATModel.sat_check_model #[%s] #[%s] 256 = some %t := by decide\n", list(c.formula), list(c.assignment), output[i] == '1')
		}
		path := filepath.Join(dir, "SATModelPins.lean")
		if err := os.WriteFile(path, []byte(pins.String()), 0600); err != nil {
			t.Fatal(err)
		}
		ctx, cancel := context.WithTimeout(context.Background(), 5*time.Minute)
		defer cancel()
		for _, args := range [][]string{{"build", "Oak.SATModel"}, {"env", "lean", path}} {
			cmd := exec.CommandContext(ctx, lake, args...)
			cmd.Dir = filepath.Join("spec", "lean")
			if out, err := cmd.CombinedOutput(); err != nil {
				t.Fatalf("Lean model replay: %v (%v)\n%s", err, ctx.Err(), out)
			}
		}
	})
}
