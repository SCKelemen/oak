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

// Signed operand positions describe the independent Tseitin specification.
// Position 1 is the gate; 2..4 are the operands. Negative means complemented.
func cnfGateClauses(kind int, e [4]uint32) [][]uint32 {
	templates := [][][]int{
		{{-1, 2}, {-1, 3}, {1, -2, -3}},
		{{1, -2}, {1, -3}, {-1, 2, 3}},
		{{-1, 2, 3}, {-1, -2, -3}, {1, -2, 3}, {1, 2, -3}},
		{{-1, -2, 3}, {-1, 2, 4}, {1, -2, -3}, {1, 2, -4}, {-1, 3, 4}, {1, -3, -4}},
	}
	var clauses [][]uint32
	for _, row := range templates[kind] {
		var clause []uint32
		for _, pos := range row {
			neg := pos < 0
			if neg {
				pos = -pos
			}
			edge := e[pos-1]
			if neg {
				edge ^= 1
			}
			clause = append(clause, edge)
		}
		clauses = append(clauses, clause)
	}
	return clauses
}

func TestOakCNFGatesCompiled(t *testing.T) {
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Fatal("C compiler required for gate regression")
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
edge_value: (edge: u32, assignment: u32): Bool =
 (((assignment >> ((edge >> u32(1)) - u32(1))) & u32(1)) == u32(1)) != ((edge & u32(1)) == u32(1))
case: (kind: u32, g: u32, x: u32, y: u32, z: u32, capacity: u32, expected: []u32): () {
 mem: [96]u32
 i: u32 = 0
 while i < len(mem) { mem[i] = u32(1000) + i; i = i + 1 }
 mem[1] = 0
 mem[4] = 3
 mem[5] = 1
 l: Layout = Layout { cap: 0, var_at: 0, low_at: 0, high_at: 0,
   unique_at: 0, umask: 0, cache_at: 0, cmask: 0, stack_at: 0,
   stack_cap: 0, bits_at: 0, selects_at: 0, select_cap: 0,
   state_at: 0, clauses_at: 32, clauses_cap: capacity, total: 96 }
 kind == u32(3) ? { cnf_emit_mux(l, span(&mem), g, x, y, z) } |
   { cnf_emit_binary(l, span(&mem), kind, g, x, y) }
 i = 0
 while i < len(mem) { assert(mem[i] == expected[i]); i = i + 1 }
 // Decode the actual final stored words and test every assignment.
 capacity == u32(64) ? {
  assignment: u32 = 0
  while assignment < u32(16) {
   at: u32 = 43
   holds: Bool = true
   while at < u32(40) + mem[4] {
    n: u32 = mem[at]
    j: u32 = 0
    clause: Bool = false
    while j < n {
     word: u32 = mem[at + u32(1) + j]
     value: Bool = ((assignment >> (word / u32(2))) & u32(1)) == u32(1)
     clause = clause || (value == (word % u32(2) == u32(1)))
     j = j + u32(1)
    }
    holds = holds && clause
    at = at + n + u32(1)
   }
   xv: Bool = edge_value(x, assignment)
   yv: Bool = edge_value(y, assignment)
   zv: Bool = edge_value(z, assignment)
   want: Bool = kind == u32(0) ? { xv && yv } | {
     kind == u32(1) ? { xv || yv } | {
      kind == u32(2) ? { xv != yv } | { xv ? { yv } | { zv } } } }
   assert(holds == (edge_value(g, assignment) == want))
   assignment = assignment + u32(1)
  }
 } | { }
}
main: (): i32 {
`)
	cases := 0
	for kind := 0; kind < 4; kind++ {
		for _, base := range [][4]uint32{{2, 4, 6, 8}, {2, 4, 4, 6}, {2, 2, 4, 4}, {2, 2, 2, 2}} {
			for mask := 0; mask < 16; mask++ {
				e := base
				for i := range e {
					e[i] ^= uint32(mask>>i) & 1
				}
				for _, capacity := range []uint32{8, 14, 21, 34, 64} {
					expected := make([]uint32, 96)
					for i := range expected {
						expected[i] = 1000 + uint32(i)
					}
					expected[1], expected[4], expected[5] = 0, 3, 1
					for _, clause := range cnfGateClauses(kind, e) {
						used := expected[4]
						n := uint32(len(clause))
						if uint64(8)+uint64(used)+uint64(n)+1 > uint64(capacity) {
							expected[1] = 1
							continue
						}
						at := 32 + 8 + used
						expected[at] = n
						for i, edge := range clause {
							expected[at+1+uint32(i)] = cnfLiteralWant(edge)
						}
						expected[4] += n + 1
						expected[5]++
					}
					fmt.Fprintf(&source, "want%d: [96]u32 = [96]u32{", cases)
					for i, v := range expected {
						if i > 0 {
							source.WriteString(",")
						}
						fmt.Fprint(&source, v)
					}
					fmt.Fprintf(&source, "}\ncase(%d,%d,%d,%d,%d,%d,view(&want%d))\n", kind, e[0], e[1], e[2], e[3], capacity, cases)
					cases++
				}
			}
		}
	}
	source.WriteString("0\n}\n")
	if err := os.WriteFile(filepath.Join(dir, "main.oak"), []byte(source.String()), 0600); err != nil {
		t.Fatal(err)
	}
	c, err := compiler.New().WithPackageDir(dir).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	cpath, bin := filepath.Join(dir, "gates.c"), filepath.Join(dir, "gates")
	if err := os.WriteFile(cpath, []byte(c), 0600); err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(t.Context(), 3*time.Minute)
	defer cancel()
	if out, err := exec.CommandContext(ctx, cc, "-std=c99", "-O1", "-o", bin, cpath, "-lm").CombinedOutput(); err != nil {
		t.Fatalf("cc: %v\n%s", err, out)
	}
	if out, err := exec.CommandContext(ctx, bin).CombinedOutput(); err != nil {
		t.Fatalf("compiled gates: %v\n%s", err, out)
	}
	t.Logf("checked %d full-buffer cases and 4096 decoded formula assignments", cases)
}

func TestOakCNFGatesLean(t *testing.T) {
	lake, err := exec.LookPath("lake")
	if err != nil {
		if os.Getenv("OAK_REQUIRE_LRAT_BINDING_LEAN") != "" {
			t.Fatal("lake required for CNF gate proof")
		}
		t.Skip("lake unavailable; formal CI requires CNF gate proof")
	}
	var contract strings.Builder
	contract.WriteString(`import Oak.CNFGates
open Oak.CNFEmission Oak.CNFGates
example (l : Layout) (mem : Array UInt32) (op g x y : UInt32) (fuel : Nat) :
    cnf_emit_binary l mem op g x y fuel = run l fuel mem (binary op g x y) :=
  binary_execution l mem op g x y fuel
example (l : Layout) (mem : Array UInt32) (g c t e : UInt32) (fuel : Nat) :
    cnf_emit_mux l mem g c t e fuel = run l fuel mem (mux g c t e) :=
  mux_execution l mem g c t e fuel
example (l : Layout) (fuel : Nat) (mem out : Array UInt32) (qs : List Clause)
    (region : l.clauses_at.toNat + l.clauses_cap.toNat < 4294967296)
    (separate : l.state_at.toNat + 6 ≤ l.clauses_at.toNat)
    (h : Admitted l fuel mem qs out) :
    ∀ j (hj : j < (words qs).length),
      out.getD (l.clauses_at.toNat + 8 + (used l mem).toNat + j) 0 = (words qs)[j] :=
  admitted_words l fuel mem out qs region separate h
example (l : Layout) (fuel : Nat) (mem out : Array UInt32)
    (op g x y : UInt32) (a : Oak.RupCheck.Assignment)
    (region : l.clauses_at.toNat + l.clauses_cap.toNat < 4294967296)
    (separate : l.state_at.toNat + 6 ≤ l.clauses_at.toNat)
    (h : Admitted l fuel mem (binary op g x y) out)
    (hg : Regular g) (hx : Regular x) (hy : Regular y) :
    cnf_emit_binary l mem op g x y fuel = some ((), out) ∧
      (BufferSatisfies a out (l.clauses_at.toNat + 8 + (used l mem).toNat) (binary op g x y) ↔
        Oak.CNFLiteral.edgeValue a g = binaryValue op
          (Oak.CNFLiteral.edgeValue a x) (Oak.CNFLiteral.edgeValue a y)) :=
  binary_production l fuel mem out op g x y a region separate h hg hx hy
example (l : Layout) (fuel : Nat) (mem out : Array UInt32)
    (g c t e : UInt32) (a : Oak.RupCheck.Assignment)
    (region : l.clauses_at.toNat + l.clauses_cap.toNat < 4294967296)
    (separate : l.state_at.toNat + 6 ≤ l.clauses_at.toNat)
    (h : Admitted l fuel mem (mux g c t e) out)
    (hg : Regular g) (hc : Regular c) (ht : Regular t) (he : Regular e) :
    cnf_emit_mux l mem g c t e fuel = some ((), out) ∧
      (BufferSatisfies a out (l.clauses_at.toNat + 8 + (used l mem).toNat) (mux g c t e) ↔
        Oak.CNFLiteral.edgeValue a g =
          (if Oak.CNFLiteral.edgeValue a c then Oak.CNFLiteral.edgeValue a t
           else Oak.CNFLiteral.edgeValue a e)) :=
  mux_production l fuel mem out g c t e a region separate h hg hc ht he
-- Constants and both sentinel polarities cannot satisfy the gate precondition.
example : ¬ Regular 0 := by unfold Regular; decide +kernel
example : ¬ Regular 1 := by unfold Regular; decide +kernel
example : ¬ Regular 4294967294 := by unfold Regular; decide +kernel
example : ¬ Regular 4294967295 := by unfold Regular; decide +kernel
example : Regular 4294967293 := by unfold Regular; decide +kernel
-- Incorrect gate values are rejected, including complemented and aliased inputs.
example : ¬ Satisfies (fun _ => true) (binary 0 3 4 6) := by
  rw [binary_semantics _ _ _ _ _ (by unfold Regular; decide +kernel)
    (by unfold Regular; decide +kernel) (by unfold Regular; decide +kernel)]
  decide +kernel
example : ¬ Satisfies (fun _ => true) (binary 1 3 4 6) := by
  rw [binary_semantics _ _ _ _ _ (by unfold Regular; decide +kernel)
    (by unfold Regular; decide +kernel) (by unfold Regular; decide +kernel)]
  decide +kernel
example : ¬ Satisfies (fun _ => true) (binary 2 2 4 4) := by
  rw [binary_semantics _ _ _ _ _ (by unfold Regular; decide +kernel)
    (by unfold Regular; decide +kernel) (by unfold Regular; decide +kernel)]
  decide +kernel
example : ¬ Satisfies (fun _ => true) (mux 3 4 6 8) := by
  rw [mux_semantics _ _ _ _ _ (by unfold Regular; decide +kernel)
    (by unfold Regular; decide +kernel) (by unfold Regular; decide +kernel)
    (by unfold Regular; decide +kernel)]
  decide +kernel

`)

	names := []string{"binary_execution", "mux_execution", "regular_flip", "regular_not_none", "flip_value", "clause_meaning", "binary_semantics", "mux_semantics", "admitted_run", "step_used", "admitted_prefix", "admitted_words", "read_records_of_words", "admitted_semantics", "binary_production", "mux_production"}
	for _, name := range names {
		fmt.Fprintf(&contract, "#print axioms Oak.CNFGates.%s\n", name)
	}
	path := filepath.Join(t.TempDir(), "CNFGatesContract.lean")
	if err := os.WriteFile(path, []byte(contract.String()), 0600); err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(t.Context(), 3*time.Minute)
	defer cancel()
	for _, args := range [][]string{{"build", "Oak.CNFGates"}, {"env", "lean", path}} {
		cmd := exec.CommandContext(ctx, lake, args...)
		cmd.Dir = filepath.Join("spec", "lean")
		out, err := cmd.CombinedOutput()
		if err != nil {
			t.Fatalf("CNF gate proof: %v\n%s", err, out)
		}
		if args[0] != "env" {
			continue
		}
		if err := cnfAxiomAudit(string(out), "Oak.CNFGates", names); err != nil {
			t.Fatalf("%v\n%s", err, out)
		}
	}
}
