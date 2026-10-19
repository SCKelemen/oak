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

func TestOakCNFObligationCompiled(t *testing.T) {
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Fatal("C compiler required for fold regression")
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
	source := `package main
obligation_value: (edge: u32, assignment: u32): Bool = edge == u32(0) ? { false } | {
 edge == u32(1) ? { true } | {
  (((assignment >> ((edge >> u32(1)) - u32(1))) & u32(1)) == u32(1)) != ((edge & u32(1)) == u32(1)) } }
case: (edges: []u32, used: u32, capacity: u32, result: u32, payload: []u32): () {
 l: Layout = Layout { cap: 8, var_at: 0, low_at: 0, high_at: 0,
 unique_at: 0, umask: 0, cache_at: 0, cmask: 0, stack_at: 0,
 stack_cap: 0, bits_at: 0, selects_at: 0, select_cap: 0,
 state_at: 200, clauses_at: 224, clauses_cap: capacity, total: 320 }
 mem: [320]u32
 want: [320]u32
 p: [11]u32
 i: u32 = 0
 while i < len(mem) { mem[i] = u32(1000)+i; i = i+u32(1) }
 i = 0
 while i < len(p) { p[i] = 0; i = i+u32(1) }
 p[u32(2)] = len(edges)
 i = 0
 while i < len(edges) { p[u32(8)+i] = i; mem[i*u32(64)] = edges[i]; i = i+u32(1) }
 mem[l.state_at+STATE_CLAUSES_USED] = used
 mem[l.state_at+STATE_CLAUSE_COUNT] = 7
 mem[l.state_at+STATE_EXCEEDED] = 0
 i = 0
 while i < len(mem) { want[i] = mem[i]; i = i+u32(1) }
 result == NONE ? { want[l.state_at+STATE_EXCEEDED] = 1 } | {
  i = 0
  while i < len(payload) {
   want[l.clauses_at+u32(9)+used+i] = payload[i]
   i = i+u32(1)
  }
  result == CNF_CLAUSE ? {
   want[l.clauses_at+u32(8)+used] = len(payload)
   want[l.state_at+STATE_CLAUSES_USED] = used+len(payload)+u32(1)
   want[l.state_at+STATE_CLAUSE_COUNT] = 8
  } | { }
 }
 assert(cnf_obligation(l,span(&mem),p[:]) == result)
 i = 0
 while i < len(mem) { assert(mem[i] == want[i]); i = i+u32(1) }
 result != NONE ? {
  assignment: u32 = 0
  while assignment < u32(4) {
   truth: Bool = false
   i = 0
   while i < len(edges) {
    root_value: Bool = obligation_value(edges[i],assignment)
    truth = truth || (i+u32(1) == len(edges) ? { !root_value } | { root_value })
    i = i+u32(1)
   }
   decoded: Bool = result == CNF_REFUTED
   result == CNF_CLAUSE ? {
    i = 0
    while i < mem[l.clauses_at+u32(8)+used] {
     word: u32 = mem[l.clauses_at+u32(9)+used+i]
     atom: Bool = ((assignment >> (word/u32(2))) & u32(1)) == u32(1)
     decoded = decoded || (atom == (word%u32(2) == u32(1)))
     i = i+u32(1)
    }
   } | { }
   assert(decoded == truth)
   assignment = assignment+u32(1)
  }
 } | { }
}
reject: (used: u32, roots: u32): () {
 mem: [32]u32
 p: [8]u32
 i: u32 = 0
 while i < len(mem) { mem[i] = u32(1000)+i; i = i+u32(1) }
 i = 0
 while i < len(p) { p[i] = 0; i = i+u32(1) }
 p[u32(2)] = roots
 l: Layout = Layout { cap: 0, var_at: 0, low_at: 0, high_at: 0,
 unique_at: 0, umask: 0, cache_at: 0, cmask: 0, stack_at: 0,
 stack_cap: 0, bits_at: 0, selects_at: 0, select_cap: 0,
 state_at: 0, clauses_at: 16, clauses_cap: 16, total: 32 }
 mem[STATE_CLAUSES_USED] = used
 assert(cnf_obligation(l,span(&mem),p[:]) == NONE)
 i = 0
 while i < len(mem) {
  expected: u32 = i == STATE_EXCEEDED ? { u32(1) } | {
   i == STATE_CLAUSES_USED ? { used } | { u32(1000)+i } }
  assert(mem[i] == expected)
  i = i+u32(1)
 }
}
layout_case: (cap: u32, terms: u32, capacity: u32, expected_bits: u32, expected_state: u32, expected_total: u32): () {
 l: Layout = layout_for_clauses(cap,terms,capacity)
 assert(l.bits_at == expected_bits)
 assert(l.state_at == expected_state)
 assert(l.clauses_at == expected_state+u32(16))
 assert(l.clauses_cap == capacity)
 assert(l.total == expected_total)
 assert(l.bits_at+terms*u32(64) <= l.clauses_at)
 assert(l.state_at+u32(5) < l.clauses_at)
}
main: (): i32 {
`
	var calls strings.Builder
	cases := 0
	for n := 0; n <= 3; n++ {
		total := 1
		for i := 0; i < n; i++ {
			total *= 6
		}
		for code := 0; code < total; code++ {
			edges := make([]uint32, n)
			v := code
			var payload []uint32
			always := false
			for i := range edges {
				edges[i] = uint32(v % 6)
				v /= 6
				lit := edges[i]
				if i == n-1 {
					lit ^= 1
				}
				always = always || lit == 1
				if lit >= 2 {
					payload = append(payload, 2*((lit>>1)-1)+1-(lit&1))
				}
			}
			result := uint32(1)
			if len(payload) > 0 {
				result = 0
			}
			if always {
				result = 2
			}
			array := func(xs []uint32) string {
				var parts []string
				for _, x := range xs {
					parts = append(parts, fmt.Sprint(x))
				}
				return "[]u32{" + strings.Join(parts, ",") + "}"
			}
			for _, used := range []uint32{0, 3} {
				for _, cap := range []uint32{8 + used + uint32(n), 9 + used + uint32(n), 12 + used + uint32(n)} {
					res := result
					if uint64(9)+uint64(used)+uint64(n) > uint64(cap) {
						res = ^uint32(0)
					}
					fmt.Fprintf(&calls, "case(%s,%d,%d,%d,%s)\n", array(edges), used, cap, res, array(payload))
					cases++
				}
			}
		}
	}
	vals := []uint32{0, 1, 7, 8, 9, 16, 2147483647, 4294967287, 4294967288, 4294967294, 4294967295}
	for _, u := range vals {
		for _, r := range vals {
			for _, c := range vals {
				fmt.Fprintf(&calls, "assert(cnf_obligation_fits(u32(%d),u32(%d),u32(%d)) == %t)\n", u, r, c, uint64(9)+uint64(u)+uint64(r) <= uint64(c))
			}
		}
	}
	for _, pair := range [][2]uint32{{4294967295, 0}, {0, 4294967295}, {4294967287, 1}, {1, 4294967287}} {
		fmt.Fprintf(&calls, "reject(u32(%d),u32(%d))\n", pair[0], pair[1])
	}
	for _, cap := range []uint32{0, 1, 2, 16, 32768} {
		u := uint32(1)
		for u < 2*cap {
			u *= 2
		}
		stack := cap
		if stack == 0 {
			stack = 1
		}
		if stack > 32768 {
			stack = 32768
		}
		bits := 3*cap + 5*u + 16*stack
		for _, terms := range []uint32{0, 1, 3} {
			state := bits + 64*terms + 16*194
			for _, capacity := range []uint32{0, 16, 128} {
				fmt.Fprintf(&calls, "layout_case(%d,%d,%d,%d,%d,%d)\n", cap, terms, capacity, bits, state, state+16+capacity)
			}
		}
	}
	source += calls.String() + "0\n}\n"

	if err := os.WriteFile(filepath.Join(dir, "main.oak"), []byte(source), 0600); err != nil {
		t.Fatal(err)
	}
	c, err := compiler.New().WithPackageDir(dir).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	cpath, bin := filepath.Join(dir, "obligation.c"), filepath.Join(dir, "obligation")
	if err := os.WriteFile(cpath, []byte(c), 0600); err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(t.Context(), 3*time.Minute)
	defer cancel()
	if out, err := exec.CommandContext(ctx, cc, "-std=c99", "-O1", "-o", bin, cpath, "-lm").CombinedOutput(); err != nil {
		t.Fatalf("cc: %v\n%s", err, out)
	}
	if out, err := exec.CommandContext(ctx, bin).CombinedOutput(); err != nil {
		t.Fatalf("compiled nodes: %v\n%s", err, out)
	}
	t.Log("checked 1554 obligation cases, 1331 mathematical guard cases, four whole-function overflow refusals, 4144 actual outcome/formula assignments, and 45 production layout cases")
}

func TestOakCNFObligationLean(t *testing.T) {
	lake, err := exec.LookPath("lake")
	if err != nil {
		if os.Getenv("OAK_REQUIRE_LRAT_BINDING_LEAN") != "" {
			t.Fatal("lake required for CNF obligation proof")
		}
		t.Skip("lake unavailable; formal CI requires CNF obligation proof")
	}
	var contract strings.Builder
	contract.WriteString(`import Oak.CNFObligation
open Oak.CNFEmission Oak.CNFObligation
example (u r c : UInt32) (fuel : Nat) :
    cnf_obligation_fits u r c fuel = some true ↔ 8+u.toNat+1+r.toNat ≤ c.toNat :=
  Oak.CNFObligation.fits_iff u r c fuel
example (l : Layout) (mem p : Array UInt32) (fuel : Nat)
    (h : cnf_obligation_fits (mem.getD (l.state_at+STATE_CLAUSES_USED).toNat 0)
      (p.getD 2 0) l.clauses_cap (fuel+1) = some false) :
    cnf_obligation l mem p (fuel+1) =
      some (NONE,mem.setIfInBounds (l.state_at+STATE_EXCEEDED).toNat 1) :=
  refused l mem p fuel h
example (a : Oak.RupCheck.Assignment) (es : List UInt32) (h : es.any (· == 1) = false) :
    Oak.RupCheck.SatisfiesClause a
      ((literals es).map (fun e => Oak.LRATRUP.decodeWord (Oak.CNFLiteral.encode e))) ↔
      es.any (Oak.CNFFolds.value a) = true := clause_meaning a es h
-- The old wrapping expression admitted both of these rejected requests.
example : ((4294967295 : UInt32)+0+1+8 ≤ 16) := by decide +kernel
example : cnf_obligation_fits 4294967295 0 16 0 = some false := by decide +kernel
example : cnf_obligation_fits 0 4294967295 16 0 = some false := by decide +kernel
example : cnf_obligation_fits 0 0 8 0 = some false := by decide +kernel
example : cnf_obligation_fits 0 0 9 0 = some true := by decide +kernel
`)
	names := []string{"fits_iff", "append_no_wrap", "finish_refused", "finish_true", "finish_empty", "finish_clause", "refused", "root_meaning", "root_start", "loop_step", "loop_done", "loop_trace", "production_trace", "consume_always", "consume_count", "reduction_semantics", "proven_meaning", "refuted_meaning", "clause_meaning"}
	for _, name := range names {
		fmt.Fprintf(&contract, "#print axioms Oak.CNFObligation.%s\n", name)
	}
	path := filepath.Join(t.TempDir(), "CNFObligationContract.lean")
	if err := os.WriteFile(path, []byte(contract.String()), 0600); err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(t.Context(), 3*time.Minute)
	defer cancel()
	for _, args := range [][]string{{"build", "Oak.CNFObligation"}, {"env", "lean", path}} {
		cmd := exec.CommandContext(ctx, lake, args...)
		cmd.Dir = filepath.Join("spec", "lean")
		out, err := cmd.CombinedOutput()
		if err != nil {
			t.Fatalf("CNF obligation proof: %v\n%s", err, out)
		}
		if args[0] != "env" {
			continue
		}
		if err := cnfAxiomAudit(string(out), "Oak.CNFObligation", names); err != nil {
			t.Fatalf("%v\n%s", err, out)
		}
	}
}
