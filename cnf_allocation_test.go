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

func TestOakCNFAllocationLean(t *testing.T) {
	lake, err := exec.LookPath("lake")
	if err != nil {
		if os.Getenv("OAK_REQUIRE_LRAT_BINDING_LEAN") != "" {
			t.Fatal("lake required for CNF allocation admission proof")
		}
		t.Skip("lake unavailable; formal CI requires CNF allocation admission proof")
	}
	var contract strings.Builder
	contract.WriteString(`import Oak.CNFAllocation
open Oak.CNFEmission Oak.CNFLayout Oak.CNFAllocation
example (cap terms u : UInt32) (fuel : Nat) :
    ∃ w, cnf_allocation_words cap terms u fuel = some w ∧
      w.toNat = requestedWords cap terms u :=
  words_exact cap terms u fuel

example (cap terms : UInt32) : ∃ b, cnf_allocation_fits cap terms 32 = some b :=
  guard_terminates cap terms

example (cap terms : UInt32) (fuel : Nat)
    (ok : cnf_allocation_fits cap terms fuel = some true) :
    ∃ u, next_pow2 (cap*2) fuel = some u ∧
      (terms+1).toNat = terms.toNat+1 ∧
      (terms*6144+65536).toNat = terms.toNat*6144+65536 ∧
      footprint cap (terms+1) (terms*6144+65536) u ≤ 1073741823 :=
  admitted_budget cap terms fuel ok

example (cap terms : UInt32) (fuel : Nat) (l : Layout)
    (ok : cnf_allocation_fits cap terms fuel = some true)
    (run : layout_for_clauses cap (terms+1) (terms*6144+65536) fuel = some l) :
    l.total.toNat ≤ 1073741823 ∧ (l.total*4).toNat = l.total.toNat*4 ∧
      l.bits_at.toNat+(terms+1).toNat*64+3104+16+(terms*6144+65536).toNat < 4294967296 :=
  allocation_safe cap terms fuel l ok run

example : cnf_allocation_fits 4096 8 32 = some true := by decide +kernel
example : cnf_allocation_fits 1073741825 0 32 = some false := by decide +kernel
example : cnf_allocation_fits 1 4294967295 32 = some false := by decide +kernel
-- Fits in words, but its byte count would wrap without the stronger bound.
example : cnf_allocation_fits 134217728 0 32 = some false := by decide +kernel
`)
	names := []string{"words_exact", "refuses_large_cap", "admitted", "guard_terminates", "admitted_budget", "allocation_safe"}
	for _, name := range names {
		fmt.Fprintf(&contract, "#print axioms Oak.CNFAllocation.%s\n", name)
	}
	path := filepath.Join(t.TempDir(), "CNFAllocationContract.lean")
	if err := os.WriteFile(path, []byte(contract.String()), 0600); err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(t.Context(), 3*time.Minute)
	defer cancel()
	for _, args := range [][]string{{"build", "Oak.CNFAllocation"}, {"env", "lean", path}} {
		cmd := exec.CommandContext(ctx, lake, args...)
		cmd.Dir = filepath.Join("spec", "lean")
		out, err := cmd.CombinedOutput()
		if err != nil {
			t.Fatalf("CNF allocation admission proof: %v\n%s", err, out)
		}
		if args[0] != "env" {
			continue
		}
		if err := cnfAxiomAudit(string(out), "Oak.CNFAllocation", names); err != nil {
			t.Fatalf("%v\n%s", err, out)
		}
	}
}

func TestOakCNFAllocationCompiled(t *testing.T) {
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Fatal("C compiler required for allocation admission regression")
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
		b, err := os.ReadFile(path)
		if err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(filepath.Join(dir, filepath.Base(path)), b, 0600); err != nil {
			t.Fatal(err)
		}
	}
	var source strings.Builder
	source.WriteString(`package main
refuse: (cap: u32, terms: u32): () {
 p: [8]u32
 p[0] = terms
 out: [8]u32
 out[0] = CERT_PROVEN
 certify_over(view(&p),u32(8),cap,span(&out))
 assert(out[0] == CERT_REFUSED)
}
main: (): i32 {
`)
	cases := 0
	caps := []uint32{0, 1, 2, 3, 4096, 32767, 32768, 32769, 33554432, 67108864, 67108865, 134217728, 268435456, 1073741824, 1073741825, 2147483648, 4294967295}
	for _, cap := range caps {
		termsCases := []uint32{0, 1, 8, 65535, 174751, 174752, 699039, 699040, 2147483648, 4294967295}
		var u uint64 = 1
		stack := uint64(cap)
		if stack == 0 {
			stack = 1
		}
		if stack > 32768 {
			stack = 32768
		}
		if cap <= 1073741824 {
			for u < 2*uint64(cap) {
				u *= 2
			}
			fixed := 3*uint64(cap) + 5*u + 16*stack + 64 + 3120 + 65536
			if fixed <= 1073741823 {
				edge := uint32((1073741823 - fixed) / 6208)
				termsCases = append(termsCases, edge, edge+1)
			}
		}
		for _, terms := range termsCases {
			words := 3*uint64(cap) + 5*u + 16*stack + 64*(uint64(terms)+1) + 3120 + 6144*uint64(terms) + 65536
			want := cap <= 1073741824 && words <= 1073741823
			fmt.Fprintf(&source, "assert(cnf_allocation_fits(u32(%d),u32(%d)) == %t)\n", cap, terms, want)
			cases++
		}
	}
	for _, pair := range [][2]uint32{{1073741825, 0}, {4294967295, 0}, {1, 4294967295}, {134217728, 0}} {
		fmt.Fprintf(&source, "refuse(u32(%d),u32(%d))\n", pair[0], pair[1])
	}
	source.WriteString("0\n}\n")
	if err := os.WriteFile(filepath.Join(dir, "main.oak"), []byte(source.String()), 0600); err != nil {
		t.Fatal(err)
	}
	c, err := compiler.New().WithPackageDir(dir).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	path, bin := filepath.Join(dir, "allocation.c"), filepath.Join(dir, "allocation")
	if err := os.WriteFile(path, []byte(c), 0600); err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(t.Context(), 3*time.Minute)
	defer cancel()
	if out, err := exec.CommandContext(ctx, cc, "-std=c99", "-O1", "-o", bin, path, "-lm").CombinedOutput(); err != nil {
		t.Fatalf("cc: %v\n%s", err, out)
	}
	if out, err := exec.CommandContext(ctx, bin).CombinedOutput(); err != nil {
		t.Fatalf("allocation admission: %v\n%s", err, out)
	}
	t.Logf("checked %d allocation guards against uint64 arithmetic and four full-caller refusals", cases)
}
