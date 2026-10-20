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

func TestOakCNFRootsLean(t *testing.T) {
	lake, err := exec.LookPath("lake")
	if err != nil {
		if os.Getenv("OAK_REQUIRE_LRAT_BINDING_LEAN") != "" {
			t.Fatal("lake required for CNF initial-root proof")
		}
		t.Skip("lake unavailable; formal CI requires CNF initial-root proof")
	}
	var contract strings.Builder
	contract.WriteString(`import Oak.CNFRoots
open Oak.CNFEmission Oak.CNFObligation Oak.CNFRoots
example (l : Layout) (initial mem p : Array UInt32) (roots at_ n r : UInt32)
    (always : Bool) (count : Nat) (remaining : r.toNat+count = roots.toNat)
    (bound : at_.toNat+1+n.toNat+count < 4294967296)
    (before : ∀ q : UInt32, q < roots → rootCell l p q < at_.toNat)
    (same : ∀ q : UInt32, q < roots → readLiteral l mem p q roots = readLiteral l initial p q roots) :
    Trace l p roots at_ mem n always r (initialLiterals l initial p roots r count) :=
  initial_trace l initial mem p roots at_ n r always count remaining bound before same
example (cap terms capacity : UInt32) (fuel : Nat) (l : Layout)
    (run : layout_for_clauses cap terms capacity fuel = some l)
    (budget : l.bits_at.toNat+terms.toNat*64+3104+16+capacity.toNat < 4294967296) :
    l.bits_at.toNat+terms.toNat*64 ≤ l.clauses_at.toNat ∧
      l.state_at.toNat+5 < l.clauses_at.toNat ∧
      l.clauses_at.toNat+l.clauses_cap.toNat = l.total.toNat ∧
      l.clauses_at.toNat+l.clauses_cap.toNat < 4294967296 :=
  constructed_regions cap terms capacity fuel l run budget
example : initialLiterals (default : Layout)
    (((Array.replicate 129 0).setIfInBounds 0 2).setIfInBounds 64 3 |>.setIfInBounds 128 4)
    #[0,0,3,0,0,0,0,0,0,1,2] 3 0 3 = [2,3,5] := by decide +kernel
-- Without the explicit budget, wrapped constructor arithmetic is not a region proof.
example : (layout_for_clauses 1 67108864 16 10).map
    (fun l => decide (l.bits_at.toNat + 67108864*64 ≤ l.clauses_at.toNat)) = some false := by decide +kernel
`)
	names := []string{"initial_length", "step_preserves_read", "initial_trace", "production_initial", "root_before_clauses", "layout_shape", "constructed_regions", "constructed_trace", "constructed_production"}
	for _, name := range names {
		fmt.Fprintf(&contract, "#print axioms Oak.CNFRoots.%s\n", name)
	}
	path := filepath.Join(t.TempDir(), "CNFRootsContract.lean")
	if err := os.WriteFile(path, []byte(contract.String()), 0600); err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(t.Context(), 3*time.Minute)
	defer cancel()
	for _, args := range [][]string{{"build", "Oak.CNFRoots"}, {"env", "lean", path}} {
		cmd := exec.CommandContext(ctx, lake, args...)
		cmd.Dir = filepath.Join("spec", "lean")
		out, err := cmd.CombinedOutput()
		if err != nil {
			t.Fatalf("CNF initial-root proof: %v\n%s", err, out)
		}
		if args[0] != "env" {
			continue
		}
		if err := cnfAxiomAudit(string(out), "Oak.CNFRoots", names); err != nil {
			t.Fatalf("%v\n%s", err, out)
		}
	}
}
