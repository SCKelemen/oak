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

// Extract from the complete production solver package, not a copied helper.
func TestOakCNFEmissionExtraction(t *testing.T) {
	extracted, err := compiler.New().WithPackageDir(filepath.Join("prove", "solver")).
		EmitLeanRoots("Oak.CNFEmission", []string{"cnf_emit", "cnf_emit_binary", "cnf_emit_mux", "cnf_apply", "cnf_ite", "cnf_obligation", "layout_for_clauses", "cnf_allocation_fits", "bdd_allocation_fits", "sat_allocation_fits", "sat_capacity_fits", "sat_layout"}).Get()
	if err != nil {
		t.Fatal(err)
	}
	if strings.Contains(extracted, "sorry") {
		t.Fatal("CNF emission extraction contains sorry")
	}
	path := filepath.Join("spec", "lean", "Oak", "CNFEmissionExtracted.lean")
	if os.Getenv("OAK_LEAN_EXTRACT_UPDATE") == "1" {
		if err := os.WriteFile(path, []byte(extracted), 0644); err != nil {
			t.Fatal(err)
		}
	}
	committed, err := os.ReadFile(path)
	if err != nil || string(committed) != extracted {
		t.Fatalf("CNF emission extraction drift (%v); regenerate with OAK_LEAN_EXTRACT_UPDATE=1", err)
	}
}

// Exercise the actual emitter with bounded buffers, including wrapped values
// which the old addition-based capacity check admitted.
func TestOakCNFEmissionCompiled(t *testing.T) {
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Fatal("C compiler required for CNF emission regression")
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
case: (used: u32, capacity: u32, n: u32, expected: []u32): () {
 mem: [96]u32
 i: u32 = 0
 while i < len(mem) { mem[i] = u32(1000) + i; i = i + 1 }
 mem[1] = 0
 mem[4] = used
 mem[5] = 7
 l: Layout = Layout { cap: 0, var_at: 0, low_at: 0, high_at: 0,
   unique_at: 0, umask: 0, cache_at: 0, cmask: 0, stack_at: 0,
   stack_cap: 0, bits_at: 0, selects_at: 0, select_cap: 0,
   state_at: 0, clauses_at: 32, clauses_cap: capacity, total: 96 }
 b: u32 = n >= 2 ? { u32(5) } | { NONE }
 c: u32 = n >= 3 ? { u32(8) } | { NONE }
 cnf_emit(l, span(&mem), u32(2), b, c)
 i = 0
 while i < len(mem) { assert(mem[i] == expected[i]); i = i + 1 }
}
main: (): i32 {
`)
	cases := 0
	for _, capacity := range []uint32{0, 7, 8, 9, 10, 11, 12, 16, 32} {
		for _, used := range []uint32{0, 1, 3, 4, 5, 8, 20, 32, 0xfffffff0, 0xfffffff6, 0xfffffff8, 0xfffffffa, 0xfffffffe, 0xffffffff} {
			for n := uint32(1); n <= 3; n++ {
				expected := make([]uint32, 96)
				for i := range expected {
					expected[i] = 1000 + uint32(i)
				}
				expected[1], expected[4], expected[5] = 0, used, 7
				fits := uint64(8)+uint64(used)+uint64(n)+1 <= uint64(capacity)
				if fits {
					at := 32 + 8 + used
					expected[at] = n
					for j, edge := range []uint32{2, 5, 8}[:n] {
						expected[int(at)+1+j] = cnfLiteralWant(edge)
					}
					expected[4], expected[5] = used+n+1, 8
				} else {
					expected[1] = 1
				}
				fmt.Fprintf(&source, "want%d: [96]u32 = [96]u32{", cases)
				for i, w := range expected {
					if i > 0 {
						source.WriteString(",")
					}
					fmt.Fprint(&source, w)
				}
				fmt.Fprintf(&source, "}\ncase(%d, %d, %d, view(&want%d))\n", used, capacity, n, cases)
				cases++
			}
		}
	}
	// The guard is also checked near the full UInt32 limit without allocating
	// fictitious multi-gigabyte buffers or executing an invalid layout.
	for _, used := range []uint32{0, 0xfffffff0, 0xfffffff4, 0xfffffff5, 0xfffffff6, 0xfffffff7, 0xffffffff} {
		for _, n := range []uint32{0, 1, 2, 3, 4, 0xffffffff} {
			for _, cap := range []uint32{0, 12, 0xfffffffe, 0xffffffff} {
				want := n >= 1 && n <= 3 && uint64(8)+uint64(used)+uint64(n)+1 <= uint64(cap)
				fmt.Fprintf(&source, "assert(cnf_clause_fits(%d, %d, %d) == %t)\n", used, n, cap, want)
			}
		}
	}
	source.WriteString("0\n}\n")
	if err := os.WriteFile(filepath.Join(dir, "main.oak"), []byte(source.String()), 0600); err != nil {
		t.Fatal(err)
	}
	generated, err := compiler.New().WithPackageDir(dir).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	cpath, bin := filepath.Join(dir, "emit.c"), filepath.Join(dir, "emit")
	if err := os.WriteFile(cpath, []byte(generated), 0600); err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(t.Context(), 2*time.Minute)
	defer cancel()
	if out, err := exec.CommandContext(ctx, cc, "-std=c99", "-O1", "-o", bin, cpath, "-lm").CombinedOutput(); err != nil {
		t.Fatalf("cc: %v\n%s", err, out)
	}
	if out, err := exec.CommandContext(ctx, bin).CombinedOutput(); err != nil {
		t.Fatalf("emitter: %v\n%s", err, out)
	}
	t.Logf("checked all 96 words after %d production emissions and 168 guard boundaries", cases)
}

func TestOakCNFEmissionLean(t *testing.T) {
	lake, err := exec.LookPath("lake")
	if err != nil {
		if os.Getenv("OAK_REQUIRE_LRAT_BINDING_LEAN") != "" {
			t.Fatal("lake required for CNF emission proof")
		}
		t.Skip("lake unavailable; formal CI requires CNF emission proof")
	}
	var contract strings.Builder
	contract.WriteString(`import Oak.CNFEmission
open Oak.CNFEmission
example (used n capacity : UInt32) (fuel : Nat) :
    cnf_clause_fits used n capacity fuel = some true ↔
      1 ≤ n.toNat ∧ n.toNat ≤ 3 ∧ 8 + used.toNat + n.toNat + 1 ≤ capacity.toNat :=
  fits_iff used n capacity fuel
example (l : Layout) (mem : Array UInt32) (a b c : UInt32) (fuel : Nat)
    (h : cnf_clause_fits (used l mem) (arity b c) l.clauses_cap fuel = some false) :
    cnf_emit l mem a b c fuel = some ((), mem.setIfInBounds (l.state_at + STATE_EXCEEDED).toNat 1) :=
  refused l mem a b c fuel h
example (l : Layout) (mem out : Array UInt32) (a b c : UInt32) (fuel : Nat)
    (accepted : cnf_clause_fits (used l mem) (arity b c) l.clauses_cap fuel = some true)
    (region : l.clauses_at.toNat + l.clauses_cap.toNat < 4294967296)
    (capacity : l.clauses_at.toNat + l.clauses_cap.toNat ≤ mem.size)
    (separate : l.state_at.toNat + 6 ≤ l.clauses_at.toNat)
    (run : cnf_emit l mem a b c fuel = some ((), out))
    (valid : ∀ e ∈ edges a b c, 2 ≤ e) (assignment : Oak.RupCheck.Assignment) :
    Oak.RupCheck.SatisfiesClause assignment
      ((readPayload out (l.clauses_at.toNat + 8 + (used l mem).toNat)
        (edges a b c).length).map Oak.LRATRUP.decodeWord) ↔
      ∃ e ∈ edges a b c, Oak.CNFLiteral.edgeValue assignment e = true :=
  production_clause l mem out a b c fuel accepted region capacity separate run valid assignment
example (u n cap count : UInt32) (fuel : Nat)
    (h : cnf_clause_fits u n cap fuel = some true) (hc : count ≤ u) :
    (u + n + 1).toNat = u.toNat + n.toNat + 1 ∧ (count + 1).toNat = count.toNat + 1 :=
  counters_no_wrap u n cap count fuel h hc
example (l : Layout) (mem out : Array UInt32) (a b c : UInt32) (fuel k : Nat)
    (h : cnf_clause_fits (used l mem) (arity b c) l.clauses_cap fuel = some true)
    (region : l.clauses_at.toNat + l.clauses_cap.toNat < 4294967296)
    (run : cnf_emit l mem a b c fuel = some ((), out))
    (outside : k < l.clauses_at.toNat + 8 + (used l mem).toNat ∨
      l.clauses_at.toNat + 8 + (used l mem).toNat + 1 + (edges a b c).length ≤ k)
    (notUsed : (l.state_at + STATE_CLAUSES_USED).toNat ≠ k)
    (notCount : (l.state_at + STATE_CLAUSE_COUNT).toNat ≠ k) :
    out.getD k 0 = mem.getD k 0 :=
  production_frame l mem out a b c fuel k h region run outside notUsed notCount
-- This is the prior overflow admission; the revised production guard refuses.
example : decide (((4294967290 : UInt32) + 1 + 1 + 8) ≤ 16) = true := by decide +kernel
example : cnf_clause_fits 4294967290 1 16 0 = some false := by decide +kernel
`)
	for _, used := range []uint32{0, 0xfffffff0, 0xfffffff4, 0xfffffff5, 0xfffffff6, 0xfffffff7, 0xffffffff} {
		for _, n := range []uint32{0, 1, 2, 3, 4, 0xffffffff} {
			for _, cap := range []uint32{0, 12, 0xfffffffe, 0xffffffff} {
				want := n >= 1 && n <= 3 && uint64(8)+uint64(used)+uint64(n)+1 <= uint64(cap)
				fmt.Fprintf(&contract, "example : cnf_clause_fits %d %d %d 0 = some %t := by decide +kernel\n", used, n, cap, want)
			}
		}
	}

	names := []string{"fits_iff", "refused", "emitted_exact", "writeWords_size", "writeWords_outside", "writeWords_read", "addresses_exact", "edges_length", "production_record", "production_clause", "counters_no_wrap", "production_frame"}
	for _, name := range names {
		fmt.Fprintf(&contract, "#print axioms Oak.CNFEmission.%s\n", name)
	}
	path := filepath.Join(t.TempDir(), "CNFEmissionContract.lean")
	if err := os.WriteFile(path, []byte(contract.String()), 0600); err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(t.Context(), 3*time.Minute)
	defer cancel()
	for _, args := range [][]string{{"build", "Oak.CNFEmission"}, {"env", "lean", path}} {
		cmd := exec.CommandContext(ctx, lake, args...)
		cmd.Dir = filepath.Join("spec", "lean")
		out, err := cmd.CombinedOutput()
		if err != nil {
			t.Fatalf("CNF emission proof: %v\n%s", err, out)
		}
		if args[0] != "env" {
			continue
		}
		if err := cnfAxiomAudit(string(out), "Oak.CNFEmission", names); err != nil {
			t.Fatalf("%v\n%s", err, out)
		}
	}
}
