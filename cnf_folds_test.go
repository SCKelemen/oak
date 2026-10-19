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

// Derive a folded edge from truth tables, independently of the production
// folder's branching order. A two-input operation folds iff one candidate
// constant/input/complement has the same truth table.
func cnfFoldWant(op, x, y uint32) uint32 {
	nodes := map[uint32]uint{}
	for _, e := range []uint32{x, y} {
		if e >= 2 {
			if _, ok := nodes[e/2]; !ok {
				nodes[e/2] = uint(len(nodes))
			}
		}
	}
	value := func(e uint32, assignment uint) bool {
		if e < 2 {
			return e == 1
		}
		return ((assignment>>nodes[e/2])&1 == 1) != (e%2 == 1)
	}
	for _, candidate := range []uint32{0, 1, x, x ^ 1, y, y ^ 1} {
		matches := true
		for a := uint(0); a < 4; a++ {
			xv, yv := value(x, a), value(y, a)
			want := xv != yv
			if op == 0 {
				want = xv && yv
			} else if op == 1 {
				want = xv || yv
			}
			if value(candidate, a) != want {
				matches = false
				break
			}
		}
		if matches {
			return candidate
		}
	}
	return ^uint32(0)
}

func TestOakCNFFoldsCompiled(t *testing.T) {
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
	var source strings.Builder
	source.WriteString(`package main
cnf_test_value: (edge: u32, assignment: u32): Bool = edge == u32(0) ? { false } | {
 edge == u32(1) ? { true } | {
  (((assignment >> ((edge >> u32(1)) - u32(1))) & u32(1)) == u32(1)) != ((edge & u32(1)) == u32(1)) } }
fold: (op: u32, x: u32, y: u32, want: u32): () {
 assert(terminal_case(op,x,y) == want)
 want != NONE ? {
  mem: [32]u32
  i: u32 = 0
  while i < len(mem) { mem[i] = u32(1000) + i; i = i + u32(1) }
  l: Layout = Layout { cap: 0, var_at: 0, low_at: 0, high_at: 0,
   unique_at: 0, umask: 0, cache_at: 0, cmask: 0, stack_at: 0,
   stack_cap: 0, bits_at: 0, selects_at: 0, select_cap: 0,
   state_at: 0, clauses_at: 0, clauses_cap: 0, total: 32 }
  assert(cnf_apply(l,span(&mem),op,x,y) == want)
  i = 0
  while i < len(mem) { assert(mem[i] == u32(1000) + i); i = i + u32(1) }
 } | { }
}
case: (mux: Bool, op: u32, c: u32, t: u32, e: u32): () {
 mem: [4096]u32
 before: [4096]u32
 i: u32 = 0
 while i < len(mem) { mem[i] = u32(1000) + i; i = i + u32(1) }
 l: Layout = layout_for_clauses(u32(16),u32(1),u32(128))
 assert(l.total <= len(mem))
 solver_init(l,span(&mem))
 assert(cnf_variable(l,span(&mem),u32(0)) == u32(2))
 assert(cnf_variable(l,span(&mem),u32(1)) == u32(4))
 assert(cnf_variable(l,span(&mem),u32(2)) == u32(6))
 i = 0
 while i < len(mem) { before[i] = mem[i]; i = i + u32(1) }
 result: u32 = mux ? { cnf_ite(l,span(&mem),c,t,e) } | { cnf_apply(l,span(&mem),op,c,t) }
 assert(!exceeded(l,span(&mem)))
 direct: Bool = mux ? {
  c == u32(0) || c == u32(1) || t == e || (t == u32(0) && e == u32(1)) || (t == u32(1) && e == u32(0))
 } | { terminal_case(op,c,t) != NONE }
 direct ? {
  i = 0
  while i < len(mem) { assert(mem[i] == before[i]); i = i + u32(1) }
 } | { }
 assignment: u32 = 0
 while assignment < u32(16) {
  cv: Bool = cnf_test_value(c,assignment)
  tv: Bool = cnf_test_value(t,assignment)
  ev: Bool = cnf_test_value(e,assignment)
  want: Bool = mux ? { cv ? { tv } | { ev } } | {
   op == u32(0) ? { cv && tv } | { op == u32(1) ? { cv || tv } | { cv != tv } } }
  at: u32 = l.clauses_at + LRAT_HEADER_WORDS
  end: u32 = at + mem[l.state_at + STATE_CLAUSES_USED]
  holds: Bool = true
  while at < end {
   n: u32 = mem[at]
   clause: Bool = false
   j: u32 = 0
   while j < n {
    word: u32 = mem[at + u32(1) + j]
    v: Bool = ((assignment >> (word / u32(2))) & u32(1)) == u32(1)
    clause = clause || (v == (word % u32(2) == u32(1)))
    j = j + u32(1)
   }
   holds = holds && clause
   at = at + n + u32(1)
  }
  assert(holds == (cnf_test_value(result,assignment) == want))
  assignment = assignment + u32(1)
 }
 used: u32 = mem[l.state_at + STATE_CLAUSES_USED]
 count: u32 = mem[l.state_at + STATE_CLAUSE_COUNT]
 nodes: u32 = mem[l.state_at + STATE_COUNT]
 again: u32 = mux ? { cnf_ite(l,span(&mem),c,t,e) } | { cnf_apply(l,span(&mem),op,c,t) }
 assert(again == result)
 assert(mem[l.state_at + STATE_CLAUSES_USED] == used)
 assert(mem[l.state_at + STATE_CLAUSE_COUNT] == count)
 assert(mem[l.state_at + STATE_COUNT] == nodes)
 assert(!exceeded(l,span(&mem)))
}
main: (): i32 {
`)
	edges := []uint32{0, 1, 2, 3, 4, 5, 0x7ffffffe, 0x7fffffff, 0xfffffffc, 0xfffffffd}
	ops := []uint32{0, 1, 2, 17, 0xffffffff}
	for _, op := range ops {
		for _, x := range edges {
			for _, y := range edges {
				fmt.Fprintf(&source, "fold(%d,%d,%d,%d)\n", op, x, y, cnfFoldWant(op, x, y))
			}
		}
	}
	for _, op := range ops {
		for x := 0; x < 8; x++ {
			for y := 0; y < 8; y++ {
				fmt.Fprintf(&source, "case(false,%d,%d,%d,0)\n", op, x, y)
			}
		}
	}
	source.WriteString(`c: u32 = 0
while c < u32(8) {
 t: u32 = 0
 while t < u32(8) {
  e: u32 = 0
  while e < u32(8) { case(true,u32(0),c,t,e); e = e + u32(1) }
  t = t + u32(1)
 }
 c = c + u32(1)
}
0
}
`)
	if err := os.WriteFile(filepath.Join(dir, "main.oak"), []byte(source.String()), 0600); err != nil {
		t.Fatal(err)
	}
	c, err := compiler.New().WithPackageDir(dir).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	cpath, bin := filepath.Join(dir, "folds.c"), filepath.Join(dir, "folds")
	if err := os.WriteFile(cpath, []byte(c), 0600); err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(t.Context(), 3*time.Minute)
	defer cancel()
	if out, err := exec.CommandContext(ctx, cc, "-std=c99", "-O1", "-o", bin, cpath, "-lm").CombinedOutput(); err != nil {
		t.Fatalf("cc: %v\n%s", err, out)
	}
	if out, err := exec.CommandContext(ctx, bin).CombinedOutput(); err != nil {
		t.Fatalf("compiled folders: %v\n%s", err, out)
	}
	t.Log("checked 500 truth-table-derived folds, 832 complete builder cases, 13312 formula assignments and repeated lookups")
}

func TestOakCNFFoldsLean(t *testing.T) {
	lake, err := exec.LookPath("lake")
	if err != nil {
		if os.Getenv("OAK_REQUIRE_LRAT_BINDING_LEAN") != "" {
			t.Fatal("lake required for CNF fold proof")
		}
		t.Skip("lake unavailable; formal CI requires CNF fold proof")
	}
	var contract strings.Builder
	contract.WriteString(`import Oak.CNFFolds
open Oak.CNFEmission Oak.CNFGates Oak.CNFFolds
example (a : Oak.RupCheck.Assignment) (op x y r : UInt32) (fuel : Nat)
    (h : terminal_case op x y fuel = some r) (hr : r ≠ NONE) :
    value a r = binaryValue op (value a x) (value a y) := terminal_sound a op x y r fuel h hr
example (l : Layout) (mem : Array UInt32) (op x y r : UInt32) (fuel : Nat)
    (h : terminal_case op x y fuel = some r) (hr : r ≠ NONE) :
    cnf_apply l mem op x y fuel = some (r, mem) := apply_folded l mem op x y r fuel h hr
example (op x y : UInt32) (fuel : Nat) (hx : Valid x) (hy : Valid y)
    (h : terminal_case op x y fuel = some NONE) :
    Regular x ∧ Regular y ∧ x ≠ y ∧ x ≠ y ^^^ 1 := terminal_residual op x y fuel hx hy h
example (l : Layout) (mem : Array UInt32) (c t e r : UInt32) (fuel : Nat)
    (h : simple c t e = some r) : cnf_ite l mem c t e fuel = some (r, mem) :=
  simple_execution l mem c t e r fuel h
example (a : Oak.RupCheck.Assignment) (c t e r : UInt32) (h : simple c t e = some r) :
    value a r = (if value a c then value a t else value a e) := simple_sound a c t e r h
example (l : Layout) (mem : Array UInt32) (c t e op x y : UInt32) (fuel : Nat)
    (hs : simple c t e = none) (hr : reduction c t e = some (op, x, y)) :
    cnf_ite l mem c t e fuel = cnf_apply l mem op x y fuel :=
  reduction_execution l mem c t e op x y fuel hs hr
example (a : Oak.RupCheck.Assignment) (c t e op x y : UInt32)
    (h : reduction c t e = some (op, x, y)) :
    binaryValue op (value a x) (value a y) = (if value a c then value a t else value a e) :=
  reduction_sound a c t e op x y h
example (c t e op x y : UInt32) (hc : Valid c) (ht : Valid t) (he : Valid e)
    (hs : simple c t e = none) (hr : reduction c t e = some (op, x, y)) :
    Regular x ∧ Regular y := reduction_regular c t e op x y hc ht he hs hr
example (c t e : UInt32) (hc : Valid c) (ht : Valid t) (he : Valid e)
    (hs : simple c t e = none) (hr : reduction c t e = none) :
    Regular c ∧ Regular t ∧ Regular e ∧ t ≠ e := mux_residual c t e hc ht he hs hr
-- The validity premise matters: a sentinel operand can masquerade as no-fold.
example : terminal_case 0 1 NONE 0 = some NONE := by decide +kernel
example : ¬ Valid NONE := by unfold Valid; decide +kernel
example : simple 2 1 0 = some 2 := by decide +kernel
example : simple 2 4 4 = some 4 := by decide +kernel
example : reduction 2 1 4 = some (OP_OR, 2, 4) := by decide +kernel
`)
	for _, op := range []uint32{0, 1, 2, 17, 0xffffffff} {
		for _, x := range []uint32{0, 1, 2, 3, 4, 5, 0x7ffffffe, 0x7fffffff, 0xfffffffc, 0xfffffffd} {
			for _, y := range []uint32{0, 1, 2, 3, 4, 5, 0x7ffffffe, 0x7fffffff, 0xfffffffc, 0xfffffffd} {
				fmt.Fprintf(&contract, "example : terminal_case %d %d %d 0 = some %d := by decide +kernel\n", op, x, y, cnfFoldWant(op, x, y))
			}
		}
	}

	names := []string{"value_false", "value_true", "value_flip", "value_regular", "terminal_sound", "apply_folded", "regular_of_valid", "valid_flip", "terminal_valid", "terminal_residual", "simple_execution", "simple_sound", "reduction_execution", "reduction_sound", "simple_valid", "reduction_regular", "mux_residual", "sorted_value"}
	for _, name := range names {
		fmt.Fprintf(&contract, "#print axioms Oak.CNFFolds.%s\n", name)
	}
	path := filepath.Join(t.TempDir(), "CNFFoldsContract.lean")
	if err := os.WriteFile(path, []byte(contract.String()), 0600); err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(t.Context(), 3*time.Minute)
	defer cancel()
	for _, args := range [][]string{{"build", "Oak.CNFFolds"}, {"env", "lean", path}} {
		cmd := exec.CommandContext(ctx, lake, args...)
		cmd.Dir = filepath.Join("spec", "lean")
		out, err := cmd.CombinedOutput()
		if err != nil {
			t.Fatalf("CNF fold proof: %v\n%s", err, out)
		}
		if args[0] != "env" {
			continue
		}
		if err := cnfAxiomAudit(string(out), "Oak.CNFFolds", names); err != nil {
			t.Fatalf("%v\n%s", err, out)
		}
	}
}
