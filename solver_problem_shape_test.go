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
)

// Keep this binding independent of the larger CNF extraction: the root is the
// actual read-only production validator, with its reachable accessors and
// constants, not a second implementation of the admission algorithm.
func TestOakProblemShapeExtraction(t *testing.T) {
	extracted, err := compiler.New().WithPackageDir(filepath.Join("prove", "solver")).
		EmitLeanRoots("Oak.ProblemShape", []string{"problem_shape_valid"}).Get()
	if err != nil {
		t.Fatal(err)
	}
	if strings.Contains(extracted, "sorry") {
		t.Fatal("problem-shape extraction contains sorry")
	}
	path := filepath.Join("spec", "lean", "Oak", "ProblemShapeExtracted.lean")
	if os.Getenv("OAK_LEAN_EXTRACT_UPDATE") == "1" {
		if err := os.WriteFile(path, []byte(extracted), 0644); err != nil {
			t.Fatal(err)
		}
	}
	committed, err := os.ReadFile(path)
	if err != nil || string(committed) != extracted {
		t.Fatalf("problem-shape extraction drift (%v); regenerate with OAK_LEAN_EXTRACT_UPDATE=1", err)
	}
}

// This corpus isolates the header/layout guard using a single well-formed
// constant and root. It does not claim coverage of every term-kind rule or
// ownership of the arena described by Layout. The production validator reads
// only the problem view, so synthetic layout offsets require no fake arena.
func TestOakProblemShapeHeaderCompiled(t *testing.T) {
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Fatal("C compiler required for problem-shape regression")
	}
	dir := t.TempDir()
	files, err := filepath.Glob(filepath.Join("prove", "solver", "*.oak"))
	if err != nil {
		t.Fatal(err)
	}
	for _, path := range files {
		if filepath.Base(path) == "main.oak" {
			continue
		}
		contents, err := os.ReadFile(path)
		if err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(filepath.Join(dir, filepath.Base(path)), contents, 0600); err != nil {
			t.Fatal(err)
		}
	}
	var source strings.Builder
	source.WriteString(`package main
check: (p: []u32, bits: u32, selects: u32, expected: Bool): () {
 l: Layout = Layout { cap: 0, var_at: 0, low_at: 0, high_at: 0,
   unique_at: 0, umask: 0, cache_at: 0, cmask: 0, stack_at: 0,
   stack_cap: 0, bits_at: bits, selects_at: selects, select_cap: 0,
   state_at: 0, clauses_at: 0, clauses_cap: 0, total: 0 }
 assert(problem_shape_valid(l, p) == expected)
}
main: (): i32 {
`)
	base := func(size int) []uint32 {
		words := make([]uint32, size)
		for i, w := range []uint32{1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1} {
			if i < len(words) {
				words[i] = w
			}
		}
		return words
	}
	cases := 0
	add := func(words []uint32, bits, selects uint32, want bool) {
		// Oak's fixed arrays have positive length. Use a real one-word owner
		// and a zero-length subslice for the empty-view negative control.
		storage := words
		if len(storage) == 0 {
			storage = []uint32{0}
		}
		fmt.Fprintf(&source, "p%d: [%d]u32 = [%d]u32{", cases, len(storage), len(storage))
		for i, word := range storage {
			if i != 0 {
				source.WriteString(",")
			}
			fmt.Fprint(&source, word)
		}
		fmt.Fprintf(&source, "}\nv%d: []u32 = view(&p%d)\ncheck(subslice(v%d, 0, %d), %d, %d, %t)\n", cases, cases, cases, len(words), bits, selects, want)
		cases++
	}
	for size := 0; size <= 24; size++ {
		add(base(size), 0, 64, size >= 17)
	}
	for _, bits := range []uint32{0, 1, 63, 64, 0xffffffbf, 0xffffffc0, 0xffffffff} {
		for _, selects := range []uint32{0, 1, 63, 64, 0xffffffbf, 0xffffffc0, 0xffffffff} {
			// Widen before subtraction in this independent oracle.
			want := uint64(selects) >= uint64(bits)+64
			add(base(17), bits, selects, want)
		}
	}
	for _, field := range []int{0, 1, 2, 4} {
		for _, count := range []uint32{2, 0x40000000, 0x80000000, 0xffffffff} {
			words := base(17)
			words[field] = count
			add(words, 0, 64, false)
		}
	}
	for _, field := range []int{0, 2} {
		words := base(17)
		words[field] = 0
		add(words, 0, 64, false)
	}
	// The budget is not a shape constraint, and trailing storage is allowed.
	words := base(24)
	words[3] = 0xffffffff
	add(words, 0, 64, true)
	source.WriteString("0\n}\n")
	if err := os.WriteFile(filepath.Join(dir, "main.oak"), []byte(source.String()), 0600); err != nil {
		t.Fatal(err)
	}
	generated, err := compiler.New().WithPackageDir(dir).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	cpath, bin := filepath.Join(dir, "shape.c"), filepath.Join(dir, "shape")
	if err := os.WriteFile(cpath, []byte(generated), 0600); err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(t.Context(), 2*time.Minute)
	defer cancel()
	if out, err := exec.CommandContext(ctx, cc, "-std=c99", "-O1", "-o", bin, cpath, "-lm").CombinedOutput(); err != nil {
		t.Fatalf("cc: %v\n%s", err, out)
	}
	if out, err := exec.CommandContext(ctx, bin).CombinedOutput(); err != nil {
		t.Fatalf("problem-shape header: %v\n%s", err, out)
	}
	t.Logf("checked %d production header/layout cases", cases)
}

func TestOakProblemShapeLean(t *testing.T) {
	lake, err := exec.LookPath("lake")
	if err != nil {
		if os.Getenv("OAK_REQUIRE_LRAT_BINDING_LEAN") != "" {
			t.Fatal("lake required for problem-shape header admission proof")
		}
		t.Skip("lake unavailable; formal CI requires problem-shape header admission proof")
	}
	var contract strings.Builder
	contract.WriteString(`import Oak.ProblemShape
open Oak.ProblemShape
example (l : Layout) (p : Array UInt32) (fuel : Nat)
    (accepted : problem_shape_valid l p fuel = some true) :
    p.size.toUInt32 ≥ 8 ∧ headerGuard l p = true :=
  header_required l p fuel accepted
example (p : Array UInt32) : (headerWords64 p).toNat = requiredWords p :=
  words_exact p
example (l : Layout) (p : Array UInt32) (fuel : Nat)
    (size : p.size < 4294967296)
    (accepted : problem_shape_valid l p fuel = some true) :
    8 ≤ p.size ∧ 0 < (p.getD 2 0).toNat ∧ requiredWords p ≤ p.size ∧
      l.bits_at.toNat + (p.getD 0 0).toNat * 64 ≤ l.selects_at.toNat :=
  admitted_header l p fuel size accepted

-- These Layout values are model inputs, not assertions of native storage.
def fixtureLayout : Layout := { (default : Layout) with selects_at := 64 }
def fixture : Array UInt32 := #[1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0]
example : problem_shape_valid fixtureLayout fixture 2 = some true := by decide +kernel
example : problem_shape_valid fixtureLayout fixture 0 = none := by decide +kernel
example : problem_shape_valid fixtureLayout #[] 0 = some false := by decide +kernel
example : problem_shape_valid { fixtureLayout with selects_at := 63 } fixture 2 = some false := by decide +kernel
example : problem_shape_valid { fixtureLayout with bits_at := 4294967295, selects_at := 0 } fixture 2 = some false := by decide +kernel
example : problem_shape_valid fixtureLayout (fixture.setIfInBounds 2 0) 2 = some false := by decide +kernel
example : problem_shape_valid fixtureLayout (fixture.setIfInBounds 4 4294967295) 2 = some false := by decide +kernel
-- Header acceptance alone does not prove full structural acceptance. A zero
-- term width passes headerGuard but is refused by the subsequent term loop.
example : headerGuard fixtureLayout (fixture.setIfInBounds 10 0) = true := by decide +kernel
example : problem_shape_valid fixtureLayout (fixture.setIfInBounds 10 0) 2 = some false := by decide +kernel
`)
	names := []string{"production_header", "header_required", "words_exact", "admitted_header"}
	for _, name := range names {
		fmt.Fprintf(&contract, "#print axioms Oak.ProblemShape.%s\n", name)
	}
	path := filepath.Join(t.TempDir(), "ProblemShapeContract.lean")
	if err := os.WriteFile(path, []byte(contract.String()), 0600); err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(t.Context(), 3*time.Minute)
	defer cancel()
	for _, args := range [][]string{{"build", "Oak.ProblemShape"}, {"env", "lean", path}} {
		cmd := exec.CommandContext(ctx, lake, args...)
		cmd.Dir = filepath.Join("spec", "lean")
		out, err := cmd.CombinedOutput()
		if err != nil {
			t.Fatalf("problem-shape header proof: %v\n%s", err, out)
		}
		if args[0] == "env" {
			if err := cnfAxiomAudit(string(out), "Oak.ProblemShape", names); err != nil {
				t.Fatalf("%v\n%s", err, out)
			}
		}
	}
}
