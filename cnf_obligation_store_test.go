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

func TestOakCNFObligationStoreLean(t *testing.T) {
	lake, err := exec.LookPath("lake")
	if err != nil {
		if os.Getenv("OAK_REQUIRE_LRAT_BINDING_LEAN") != "" {
			t.Fatal("lake required for CNF obligation storage proof")
		}
		t.Skip("lake unavailable; formal CI requires CNF obligation storage proof")
	}
	var contract strings.Builder
	contract.WriteString(`import Oak.CNFObligationStore
open Oak.CNFEmission Oak.CNFObligation Oak.CNFObligationStore
example (mem : Array UInt32) (at_ n : UInt32) (always : Bool) (es : List UInt32)
    (bound : at_.toNat+1+n.toNat+(literals es).length < 4294967296) :
    (consume mem at_ n always es).1 = writeWords mem (at_.toNat+1+n.toNat) (words es) :=
  consume_words mem at_ n always es bound
example (a : Oak.RupCheck.Assignment) (out : Array UInt32) (at_ : Nat) (es : List UInt32)
    (header : (out.getD at_ 0).toNat = (literals es).length)
    (cells : ∀ j (h : j < (words es).length), out.getD (at_+1+j) 0 = (words es)[j])
    (noTrue : es.any (· == 1) = false) :
    Oak.RupCheck.SatisfiesClause a
      ((Oak.CNFEmission.readPayload out at_ (out.getD at_ 0).toNat).map Oak.LRATRUP.decodeWord) ↔
      es.any (Oak.CNFFolds.value a) = true := stored_semantics a out at_ es header cells noTrue
-- Concrete readback includes constants and complemented edges.
example : Oak.CNFEmission.readPayload (consume (Array.replicate 16 99) 3 0 false [0,2,1,3,0,4]).1 3 3 = [1,0,3] := by decide +kernel
-- Counter/payload aliasing really can corrupt a literal; separation is essential.
def aliasLayout : Layout := default
example : (commit aliasLayout ((Array.replicate 16 99).setIfInBounds 4 77) 3 0 1).getD 4 0 = 2 := by decide +kernel
example : (commit aliasLayout ((Array.replicate 16 99).setIfInBounds 4 77) 3 0 1).getD 4 0 ≠ 77 := by decide +kernel
`)
	names := []string{"layout_bounds", "state_separation", "consume_words", "consume_read", "consume_frame", "root_read_preserved", "commit_payload", "commit_header", "published_payload", "published_header", "production_record", "readPayload_exact", "stored_semantics"}
	for _, name := range names {
		fmt.Fprintf(&contract, "#print axioms Oak.CNFObligationStore.%s\n", name)
	}
	path := filepath.Join(t.TempDir(), "CNFObligationStoreContract.lean")
	if err := os.WriteFile(path, []byte(contract.String()), 0600); err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(t.Context(), 3*time.Minute)
	defer cancel()
	for _, args := range [][]string{{"build", "Oak.CNFObligationStore"}, {"env", "lean", path}} {
		cmd := exec.CommandContext(ctx, lake, args...)
		cmd.Dir = filepath.Join("spec", "lean")
		out, err := cmd.CombinedOutput()
		if err != nil {
			t.Fatalf("CNF obligation storage proof: %v\n%s", err, out)
		}
		if args[0] != "env" {
			continue
		}
		if err := cnfAxiomAudit(string(out), "Oak.CNFObligationStore", names); err != nil {
			t.Fatalf("%v\n%s", err, out)
		}
	}
}
