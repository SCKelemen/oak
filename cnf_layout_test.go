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
)

func TestOakCNFLayoutLean(t *testing.T) {
	lake, err := exec.LookPath("lake")
	if err != nil {
		if os.Getenv("OAK_REQUIRE_LRAT_BINDING_LEAN") != "" {
			t.Fatal("lake required for CNF complete-layout proof")
		}
		t.Skip("lake unavailable; formal CI requires CNF complete-layout proof")
	}
	var contract strings.Builder
	contract.WriteString(`import Oak.CNFLayout
open Oak.CNFEmission Oak.CNFLayout
example (n : UInt32) (small : n.toNat ≤ 2147483648) :
    ∃ q, next_pow2 n 32 = some q ∧ n.toNat ≤ q.toNat ∧ 0 < q.toNat ∧ q.toNat ≤ 2147483648 :=
  next_pow2_terminates n small

example (cap terms capacity : UInt32)
    (small : cap.toNat ≤ 1073741824) :
    ∃ u l, next_pow2 (cap*2) 32 = some u ∧ layout_for_clauses cap terms capacity 32 = some l ∧
      2*cap.toNat ≤ u.toNat ∧ 0 < u.toNat ∧ u.toNat ≤ 2147483648 :=
  constructor_terminates cap terms capacity small

example (cap terms capacity u : UInt32) (fuel : Nat) (l : Layout)
    (pow : next_pow2 (cap*2) fuel = some u)
    (run : layout_for_clauses cap terms capacity fuel = some l)
    (budget : footprint cap terms capacity u < 4294967296) :
    l.var_at.toNat+cap.toNat = l.low_at.toNat ∧
      l.low_at.toNat+cap.toNat = l.high_at.toNat ∧
      l.high_at.toNat+cap.toNat = l.unique_at.toNat ∧
      l.unique_at.toNat+u.toNat = l.cache_at.toNat ∧
      l.cache_at.toNat+4*u.toNat = l.stack_at.toNat ∧
      l.stack_at.toNat+16*(stackSlots cap).toNat = l.bits_at.toNat ∧
      l.bits_at.toNat+64*terms.toNat = l.selects_at.toNat ∧
      l.selects_at.toNat+3104 = l.state_at.toNat ∧
      l.state_at.toNat+16 = l.clauses_at.toNat ∧
      l.clauses_at.toNat+capacity.toNat = l.total.toNat ∧
      l.total.toNat = footprint cap terms capacity u :=
  complete_regions cap terms capacity u fuel l pow run budget

example (cap terms capacity u : UInt32) (fuel : Nat) (l : Layout)
    (pow : next_pow2 (cap*2) fuel = some u)
    (run : layout_for_clauses cap terms capacity fuel = some l)
    (budget : footprint cap terms capacity u < 4294967296) :
    l.bits_at.toNat+terms.toNat*64+3104+16+capacity.toNat < 4294967296 :=
  suffix_budget cap terms capacity u fuel l pow run budget

example : next_pow2 2147483648 32 = some 2147483648 := by decide +kernel
example : next_pow2 2147483649 64 = none := by decide +kernel
example : footprint 0 0 0 1 = 3141 := by decide +kernel
-- A terminating constructor can still wrap if the allocation budget is omitted.
example : (layout_for_clauses 536870912 0 0 32).map
    (fun l => decide (l.total.toNat = footprint 536870912 0 0 1073741824)) = some false := by decide +kernel
`)
	names := []string{"pow2_loop", "next_pow2_terminates", "prefix_shape", "prefix_regions", "complete_regions", "constructor_terminates", "suffix_budget"}
	for _, name := range names {
		fmt.Fprintf(&contract, "#print axioms Oak.CNFLayout.%s\n", name)
	}
	path := filepath.Join(t.TempDir(), "CNFLayoutContract.lean")
	if err := os.WriteFile(path, []byte(contract.String()), 0600); err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(t.Context(), 3*time.Minute)
	defer cancel()
	for _, args := range [][]string{{"build", "Oak.CNFLayout"}, {"env", "lean", path}} {
		cmd := exec.CommandContext(ctx, lake, args...)
		cmd.Dir = filepath.Join("spec", "lean")
		out, err := cmd.CombinedOutput()
		if err != nil {
			t.Fatalf("CNF complete-layout proof: %v\n%s", err, out)
		}
		if args[0] != "env" {
			continue
		}
		if err := cnfAxiomAudit(string(out), "Oak.CNFLayout", names); err != nil {
			t.Fatalf("%v\n%s", err, out)
		}
	}
}
