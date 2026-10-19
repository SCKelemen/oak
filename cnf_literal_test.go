package main

import (
	"context"
	"fmt"
	"math/rand"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/SCKelemen/oak/compiler"
)

// Extract from the complete production solver package, not a copied helper.
func TestOakCNFLiteralExtraction(t *testing.T) {
	extracted, err := compiler.New().WithPackageDir(filepath.Join("prove", "solver")).
		EmitLeanRoots("Oak.CNFLiteral", []string{"cnf_lit"}).Get()
	if err != nil {
		t.Fatal(err)
	}
	if strings.Contains(extracted, "sorry") {
		t.Fatal("CNF literal extraction contains sorry")
	}
	path := filepath.Join("spec", "lean", "Oak", "CNFLiteralExtracted.lean")
	if os.Getenv("OAK_LEAN_EXTRACT_UPDATE") == "1" {
		if err := os.WriteFile(path, []byte(extracted), 0644); err != nil {
			t.Fatal(err)
		}
	}
	committed, err := os.ReadFile(path)
	if err != nil || string(committed) != extracted {
		t.Fatalf("CNF literal extraction drift (%v); regenerate with OAK_LEAN_EXTRACT_UPDATE=1", err)
	}
}

func cnfLiteralCases() []uint32 {
	edges := []uint32{0, 1, 2, 3, 4, 5, 0x7ffffffe, 0x7fffffff, 0x80000000, 0x80000001, 0xfffffffc, 0xfffffffd, 0xfffffffe, 0xffffffff}
	rng := rand.New(rand.NewSource(20261019))
	for i := 0; i < 256; i++ {
		edges = append(edges, rng.Uint32())
	}
	return edges
}

// Independent mathematical oracle: positive edges map to odd literal words,
// complemented edges to even words. Constants deliberately have no literal.
func cnfLiteralWant(edge uint32) uint32 {
	if edge < 2 {
		return ^uint32(0) - edge
	}
	node := uint64(edge) / 2
	polarity := uint64(1)
	if edge%2 == 1 {
		polarity = 0
	}
	return uint32(2*(node-1) + polarity)
}

func TestOakCNFLiteralCompiled(t *testing.T) {
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Fatal("C compiler required for CNF literal regression")
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
	source.WriteString("package main\nmain: (): i32 {\n")
	edges := cnfLiteralCases()
	fmt.Fprintf(&source, "edges: [%d]u32 = [%d]u32{", len(edges), len(edges))
	for i, edge := range edges {
		if i != 0 {
			source.WriteString(",")
		}
		fmt.Fprint(&source, edge)
	}
	fmt.Fprintf(&source, "}\nexpected: [%d]u32 = [%d]u32{", len(edges), len(edges))
	for i, edge := range edges {
		if i != 0 {
			source.WriteString(",")
		}
		fmt.Fprint(&source, cnfLiteralWant(edge))
	}
	source.WriteString("}\ni: u32 = 0\nwhile i < len(edges) {\nassert(cnf_lit(edges[i]) == expected[i])\ni = i + 1\n}\n")
	source.WriteString("0\n}\n")
	if err := os.WriteFile(filepath.Join(dir, "main.oak"), []byte(source.String()), 0600); err != nil {
		t.Fatal(err)
	}
	generated, err := compiler.New().WithPackageDir(dir).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	cpath, bin := filepath.Join(dir, "literal.c"), filepath.Join(dir, "literal")
	if err := os.WriteFile(cpath, []byte(generated), 0600); err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(t.Context(), 2*time.Minute)
	defer cancel()
	if out, err := exec.CommandContext(ctx, cc, "-std=c99", "-O1", "-o", bin, cpath, "-lm").CombinedOutput(); err != nil {
		t.Fatalf("cc: %v\n%s", err, out)
	}
	if out, err := exec.CommandContext(ctx, bin).CombinedOutput(); err != nil {
		t.Fatalf("compiled encoder: %v\n%s", err, out)
	}
	t.Logf("checked %d production literal encodings", len(cnfLiteralCases()))
}

func TestOakCNFLiteralLean(t *testing.T) {
	lake, err := exec.LookPath("lake")
	if err != nil {
		if os.Getenv("OAK_REQUIRE_LRAT_BINDING_LEAN") != "" {
			t.Fatal("lake required for CNF literal proof")
		}
		t.Skip("lake unavailable; formal CI requires CNF literal proof")
	}
	var contract strings.Builder
	contract.WriteString(`import Oak.CNFLiteral
open Oak.CNFLiteral
example (edge : UInt32) (fuel : Nat) :
    cnf_lit edge fuel = some (encode edge) := extracted edge fuel
example (edge : UInt32) (h : 2 ≤ edge) :
    Oak.LRATRUP.decodeWord (encode edge) =
      ⟨((edge >>> 1) - 1).toNat, edge &&& 1 == 0⟩ := decode_exact edge h
example (a : Oak.RupCheck.Assignment) (edges : List UInt32)
    (h : ∀ e ∈ edges, 2 ≤ e) :
    Oak.RupCheck.SatisfiesClause a
      (edges.map (fun e => Oak.LRATRUP.decodeWord (encode e))) ↔
      ∃ e ∈ edges, edgeValue a e = true := clause_semantics a edges h
-- Constant edges must be folded before emission; they cannot use decode_exact.
example : (Oak.LRATRUP.decodeWord (encode 0)).index ≠ 0 := by decide +kernel
example : (Oak.LRATRUP.decodeWord (encode 1)).index ≠ 0 := by decide +kernel
`)
	for _, edge := range cnfLiteralCases() {
		fmt.Fprintf(&contract, "example : cnf_lit %d 0 = some %d := by decide +kernel\n", edge, cnfLiteralWant(edge))
	}
	names := []string{"extracted", "index_word", "polarity_word", "decode_exact", "literal_semantics", "clause_semantics"}
	for _, name := range names {
		fmt.Fprintf(&contract, "#print axioms Oak.CNFLiteral.%s\n", name)
	}
	path := filepath.Join(t.TempDir(), "CNFLiteralContract.lean")
	if err := os.WriteFile(path, []byte(contract.String()), 0600); err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(t.Context(), 3*time.Minute)
	defer cancel()
	for _, args := range [][]string{{"build", "Oak.CNFLiteral"}, {"env", "lean", path}} {
		cmd := exec.CommandContext(ctx, lake, args...)
		cmd.Dir = filepath.Join("spec", "lean")
		out, err := cmd.CombinedOutput()
		if err != nil {
			t.Fatalf("CNF literal proof: %v\n%s", err, out)
		}
		if args[0] != "env" {
			continue
		}
		audited := 0
		for _, line := range strings.Split(string(out), "\n") {
			if strings.Contains(line, "does not depend on any axioms") {
				audited++
				continue
			}
			_, axioms, found := strings.Cut(line, "depends on axioms: [")
			if !found {
				continue
			}
			audited++
			for _, axiom := range strings.Split(strings.TrimSuffix(strings.TrimSpace(axioms), "]"), ",") {
				switch strings.TrimSpace(axiom) {
				case "", "propext", "Classical.choice", "Quot.sound":
				default:
					t.Fatalf("unexpected CNF literal axiom: %s", line)
				}
			}
		}
		if audited != len(names) {
			t.Fatalf("audited %d/%d theorem closures\n%s", audited, len(names), out)
		}
	}
}
