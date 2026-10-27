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

// Fixed contracts prevent the global table invariant from quietly weakening
// into just a local write/readback statement. The axiom audit is mandatory in CI.
func TestOakCNFTableLean(t *testing.T) {
	lake, err := exec.LookPath("lake")
	if err != nil {
		if os.Getenv("OAK_REQUIRE_LRAT_BINDING_LEAN") != "" {
			t.Fatal("lake required for CNF table invariant")
		}
		t.Skip("lake unavailable; formal CI requires CNF table invariant")
	}
	var contract strings.Builder
	contract.WriteString(`import Oak.CNFTable
open Oak.CNFEmission Oak.CNFNodes Oak.CNFTable
example (l : Layout) (mem : Array UInt32) (key a b h n : UInt32)
    (wf : WellFormed l mem n) (safe : Footprint l mem h n)
    (within : h.toNat ≤ l.umask.toNat) (vacant : slot l mem h = 0)
    (room : n < l.cap) (limit : l.cap.toNat ≤ 2147483647) :
    WellFormed l (allocate l mem key a b h n) (n+1) :=
  allocate_preserves l mem key a b h n wf safe within vacant room limit
example (l : Layout) (mem : Array UInt32) (key a b h n remaining : UInt32)
    (fuel : Nat) (wf : WellFormed l mem n) (safe : Footprint l mem h n)
    (within : h.toNat ≤ l.umask.toNat) (vacant : slot l mem h = 0)
    (room : n < l.cap) (limit : l.cap.toNat ≤ 2147483647)
    (running : mem.getD (l.state_at + STATE_EXCEEDED).toNat 0 = 0) :
    ∃ after, cnf_node.loop1 l mem key a b h NONE remaining (fuel+2) =
      some (after, h, n, remaining) ∧ WellFormed l after (n+1) :=
  fresh_preserves l mem key a b h n remaining fuel wf safe within vacant room limit running
example (l : Layout) (mem : Array UInt32) (n s : UInt32)
    (wf : WellFormed l mem n) (within : s.toNat ≤ l.umask.toNat)
    (occupied : slot l mem s ≠ 0) :
    1 ≤ (slot l mem s - 1).toNat ∧ (slot l mem s - 1).toNat < n.toNat :=
  live_reference l mem n s wf within occupied
example (l : Layout) (mem : Array UInt32) (key a b h n remaining : UInt32)
    (fuel : Nat) (wf : WellFormed l mem n) (within : h.toNat ≤ l.umask.toNat)
    (occupied : slot l mem h ≠ 0)
    (hit : Matches l mem key a b (slot l mem h - 1))
    (running : mem.getD (l.state_at + STATE_EXCEEDED).toNat 0 = 0) :
    cnf_node.loop1 l mem key a b h NONE remaining (fuel+2) =
      some (mem, h, slot l mem h - 1, remaining) ∧ WellFormed l mem n :=
  reuse_preserves l mem key a b h n remaining fuel wf within occupied hit running
-- Distinct occupied slots cannot alias one node. This checks that uniqueness
-- is part of the maintained invariant, not merely a comment.
example (l : Layout) (mem : Array UInt32) (n s t : UInt32)
    (wf : WellFormed l mem n) (hs : s.toNat ≤ l.umask.toNat)
    (ht : t.toNat ≤ l.umask.toNat) (hne : s ≠ t)
    (occupied : slot l mem s ≠ 0) : slot l mem s ≠ slot l mem t := by
  intro same; exact hne (wf.unique s t hs ht occupied same)
-- Every allocated nonzero index must still have a table slot after insertion.
example (l : Layout) (mem : Array UInt32) (n e : UInt32)
    (wf : WellFormed l mem n) (lo : 2 ≤ e.toNat) (hi : e.toNat ≤ n.toNat) :
    ∃ s : UInt32, s.toNat ≤ l.umask.toNat ∧ slot l mem s = e :=
  wf.covers e lo hi
`)
	names := []string{"other_slot", "empty", "allocate_preserves", "fresh_preserves", "live_reference", "reuse_preserves"}
	for _, name := range names {
		fmt.Fprintf(&contract, "#print axioms Oak.CNFTable.%s\n", name)
	}
	path := filepath.Join(t.TempDir(), "CNFTableContract.lean")
	if err := os.WriteFile(path, []byte(contract.String()), 0600); err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(t.Context(), 3*time.Minute)
	defer cancel()
	for _, args := range [][]string{{"build", "Oak.CNFTable"}, {"env", "lean", path}} {
		cmd := exec.CommandContext(ctx, lake, args...)
		cmd.Dir = filepath.Join("spec", "lean")
		out, err := cmd.CombinedOutput()
		if err != nil {
			t.Fatalf("CNF table invariant: %v\n%s", err, out)
		}
		if args[0] == "env" {
			if err := cnfAxiomAudit(string(out), "Oak.CNFTable", names); err != nil {
				t.Fatalf("%v\n%s", err, out)
			}
		}
	}
}
