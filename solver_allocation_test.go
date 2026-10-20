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

func TestOakSolverAllocationLean(t *testing.T) {
	lake, err := exec.LookPath("lake")
	if err != nil {
		if os.Getenv("OAK_REQUIRE_LRAT_BINDING_LEAN") != "" {
			t.Fatal("lake required for solver allocation admission proof")
		}
		t.Skip("lake unavailable; formal CI requires solver allocation admission proof")
	}
	var contract strings.Builder
	contract.WriteString(`import Oak.SolverAllocation
open Oak.CNFEmission Oak.CNFLayout Oak.SolverAllocation
example (vars clauses store record : UInt32) (fuel : Nat) :
    sat_allocation_fits vars clauses store record fuel = some true ↔ satWords vars clauses store record ≤ 1073741823 :=
  sat_admitted vars clauses store record fuel

example (clauses literals : UInt32) (fuel : Nat)
    (ok : sat_capacity_fits clauses literals fuel = some true) :
    (8*clauses+65536).toNat = 8*clauses.toNat+65536 ∧
      (64*literals+1048576).toNat = 64*literals.toNat+1048576 ∧
      (8+literals).toNat = 8+literals.toNat :=
  capacity_admitted clauses literals fuel ok

example (vars clauses store record : UInt32) (fuel : Nat) (l : SatLayout)
    (ok : sat_allocation_fits vars clauses store record fuel = some true)
    (run : sat_layout vars clauses store record fuel = some l) :
    l.total.toNat = satWords vars clauses store record :=
  sat_layout_total vars clauses store record fuel l ok run

example (vars clauses store record : UInt32) (fuel : Nat) (l : SatLayout)
    (ok : sat_allocation_fits vars clauses store record fuel = some true)
    (run : sat_layout vars clauses store record fuel = some l) :
    l.total.toNat ≤ 1073741823 ∧ (l.total*4).toNat = l.total.toNat*4 :=
  sat_bytes_safe vars clauses store record fuel l ok run

example (cap terms variants : UInt32) (fuel : Nat)
    (ok : bdd_allocation_fits cap terms variants fuel = some true) :
    cap.toNat ≤ 1073741824 ∧ 1 ≤ variants.toNat ∧ variants.toNat ≤ 3 ∧
      ∃ u, next_pow2 (cap*2) fuel = some u ∧ bddWords cap terms u variants ≤ 1073741823 :=
  bdd_admitted cap terms variants fuel ok

example (cap terms variants : UInt32) (fuel : Nat) (l : Layout)
    (ok : bdd_allocation_fits cap terms variants fuel = some true)
    (run : layout_for cap terms fuel = some l) :
    let extra : UInt32 := if variants > 1 then 32768 else 0
    (l.total+extra).toNat = l.total.toNat+extra.toNat ∧
      (l.total+extra).toNat ≤ 1073741823 ∧
      ((l.total+extra)*4).toNat = (l.total.toNat+extra.toNat)*4 :=
  bdd_bytes_safe cap terms variants fuel l ok run

example : bdd_allocation_fits 1073741825 0 1 32 = some false := by decide +kernel
example : bdd_allocation_fits 1 0 4 32 = some false := by decide +kernel
example : sat_allocation_fits 4294967295 0 0 0 0 = some false := by decide +kernel
example : sat_capacity_fits 536862720 0 0 = some false := by decide +kernel
`)
	names := []string{"bdd_words_exact", "sat_words_exact", "sat_admitted", "capacity_admitted", "bdd_admitted", "sat_layout_total", "sat_bytes_safe", "bdd_bytes_safe"}
	for _, name := range names {
		fmt.Fprintf(&contract, "#print axioms Oak.SolverAllocation.%s\n", name)
	}
	path := filepath.Join(t.TempDir(), "SolverAllocationContract.lean")
	if err := os.WriteFile(path, []byte(contract.String()), 0600); err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(t.Context(), 3*time.Minute)
	defer cancel()
	for _, args := range [][]string{{"build", "Oak.SolverAllocation"}, {"env", "lean", path}} {
		cmd := exec.CommandContext(ctx, lake, args...)
		cmd.Dir = filepath.Join("spec", "lean")
		out, err := cmd.CombinedOutput()
		if err != nil {
			t.Fatalf("solver allocation admission proof: %v\n%s", err, out)
		}
		if args[0] != "env" {
			continue
		}
		if err := cnfAxiomAudit(string(out), "Oak.SolverAllocation", names); err != nil {
			t.Fatalf("%v\n%s", err, out)
		}
	}
}

func TestOakSolverAllocationCompiled(t *testing.T) {
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
bdd_refuse: (terms: u32, variants: u32): () {
 lw: Lower = lower_layout(u32(0),u32(0))
 raw: c.Ptr = malloc(c.Size(lw.built_total*u32(4)))
 assert(raw != c.null())
 unsafe {
  built: Buffer[u32] = c.own[u32](raw,lw.built_total)
  span(&built)[0] = terms
  released: c.Ptr = c.disown(built)
 }
 out: [520]u32
 out[0] = u32(0)
 race_bounded(lw,raw,raw,raw,u32(8),u32(8),u32(8),variants,u32(4096),span(&out))
 assert(out[0] == STATUS_EXCEEDED)
 assert(out[518] == u32(0))
 assert(out[519] == u32(0))
 free(raw)
}
capacity_case: (clauses: u32, literals: u32, expected: Bool): () {
 header: [8]u32
 header[2] = clauses
 header[3] = literals
 assert(cnf_sat_capacity_fits(span(&header),u32(0)) == expected)
}
main: (): i32 {
`)
	cases := 0
	for _, cap := range []uint32{0, 1, 3, 4096, 32767, 32768, 32769, 67108864, 67108865, 1073741824, 1073741825, 4294967295} {
		u := uint64(1)
		if cap <= 1073741824 {
			for u < 2*uint64(cap) {
				u *= 2
			}
		}
		stack := uint64(cap)
		if stack == 0 {
			stack = 1
		}
		if stack > 32768 {
			stack = 32768
		}
		for _, variants := range []uint32{0, 1, 2, 3, 4} {
			extra := uint64(0)
			if variants > 1 {
				extra = 32768
			}
			fixed := 3*uint64(cap) + 5*u + 16*stack + 3120 + extra
			termsCases := []uint32{0, 1, 100, 16777215, 4294967295}
			if fixed <= 1073741823 {
				edge := uint32((1073741823 - fixed) / 64)
				termsCases = append(termsCases, edge, edge+1)
			}
			for _, terms := range termsCases {
				want := cap <= 1073741824 && variants >= 1 && variants <= 3 && fixed+64*uint64(terms) <= 1073741823
				fmt.Fprintf(&source, "assert(bdd_allocation_fits(u32(%d),u32(%d),u32(%d)) == %t)\n", cap, terms, variants, want)
				cases++
			}
		}
	}
	vals := []uint32{0, 1, 64, 1000000, 1073741823, 4294967295}
	for _, v := range vals {
		for _, c := range vals {
			for _, s := range vals {
				for _, r := range vals {
					words := 23*(uint64(v)+1) + 10*uint64(c) + 3*uint64(s) + uint64(r) + 50
					want := words <= 1073741823
					fmt.Fprintf(&source, "assert(sat_allocation_fits(u32(%d),u32(%d),u32(%d),u32(%d)) == %t)\n", v, c, s, r, want)
					if want {
						fmt.Fprintf(&source, "assert(sat_layout(u32(%d),u32(%d),u32(%d),u32(%d)).total == u32(%d))\n", v, c, s, r, words)
					}
					cases++
				}
			}
		}
	}
	for _, c := range []uint32{0, 536862719, 536862720, 4294967295} {
		for _, l := range []uint32{0, 67092479, 67092480, 4294967295} {
			want := uint64(c)*8+65536 <= 4294967295 && uint64(l)*64+1048576 <= 4294967295
			fmt.Fprintf(&source, "capacity_case(u32(%d),u32(%d),%t)\n", c, l, want)
			cases++
		}
	}
	for _, record := range []uint32{1073741750, 1073741751} {
		fmt.Fprintf(&source, "assert(sat_allocation_fits(u32(0),u32(0),u32(0),u32(%d)) == %t)\n", record, record == 1073741750)
		cases++
	}
	source.WriteString("bdd_refuse(u32(4294967295),u32(1))\nbdd_refuse(u32(0),u32(0))\nbdd_refuse(u32(0),u32(4))\n")

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
	t.Logf("checked %d allocation guards against uint64 arithmetic and three BDD caller refusals", cases)
}
