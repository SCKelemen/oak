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

func TestOakCNFNodesCompiled(t *testing.T) {
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
case: (start: u32, collisions: u32, mode: u32): () {
 l: Layout = Layout { cap: 8, var_at: 0, low_at: 16, high_at: 32,
 unique_at: 48, umask: 7, cache_at: 0, cmask: 0, stack_at: 0,
 stack_cap: 0, bits_at: 0, selects_at: 0, select_cap: 0,
 state_at: 64, clauses_at: 80, clauses_cap: 16, total: 96 }
 mem: [96]u32
 want: [96]u32
 i: u32 = 0
 while i < len(mem) { mem[i] = u32(1000)+i; i = i+u32(1) }
 i = 0
 while i < u32(8) { mem[l.unique_at+i] = 0; i = i+u32(1) }
 key: u32 = 0
 while (hash3(key,u32(12),u32(14)) & l.umask) != start { key = key+u32(1) }
 i = 0
 while i < collisions {
  mem[l.unique_at+((start+i)&l.umask)] = i+u32(2)
  mem[l.var_at+i+u32(1)] = key+u32(1)
  i = i+u32(1)
 }
 n: u32 = collisions+u32(1)
 mem[l.state_at+STATE_COUNT] = mode == u32(2) ? { l.cap } | { n }
 mem[l.state_at+STATE_EXCEEDED] = mode == u32(3) ? { u32(1) } | { u32(0) }
 mem[l.state_at+STATE_CREATED] = 19
 slot: u32 = (start+collisions)&l.umask
 mode == u32(1) ? {
  mem[l.unique_at+slot] = u32(8)
  mem[l.var_at+u32(7)] = key
  mem[l.low_at+u32(7)] = 12
  mem[l.high_at+u32(7)] = 14
  mem[l.state_at+STATE_COUNT] = l.cap
 } | { }
 i = 0
 while i < len(mem) { want[i] = mem[i]; i = i+u32(1) }
 want[l.state_at+STATE_CREATED] = 0
 result: u32 = NONE
 mode == u32(0) ? {
  result = n
  want[l.var_at+n] = key
  want[l.low_at+n] = 12
  want[l.high_at+n] = 14
  want[l.unique_at+slot] = n+u32(1)
  want[l.state_at+STATE_COUNT] = n+u32(1)
  want[l.state_at+STATE_CREATED] = 1
 } | {
  mode == u32(1) ? { result = 7 } | {
   mode == u32(2) ? { want[l.state_at+STATE_EXCEEDED] = 1 } | { }
  }
 }
 assert(cnf_node(l,span(&mem),key,u32(12),u32(14)) == result)
 i = 0
 while i < len(mem) { assert(mem[i] == want[i]); i = i+u32(1) }
}
// A full unique table with no matching key used to spin forever. Verify
// every start slot, final-slot reuse, and invalid node indices fail closed.
full_case: (start: u32, mode: u32): () {
 l: Layout = Layout { cap: 8, var_at: 0, low_at: 16, high_at: 32,
 unique_at: 48, umask: 7, cache_at: 0, cmask: 0, stack_at: 0,
 stack_cap: 0, bits_at: 0, selects_at: 0, select_cap: 0,
 state_at: 64, clauses_at: 80, clauses_cap: 16, total: 96 }
 mem: [96]u32
 want: [96]u32
 i: u32 = 0
 while i < len(mem) { mem[i] = u32(1000)+i; i = i+u32(1) }
 key: u32 = 0
 while (hash3(key,u32(12),u32(14)) & l.umask) != start { key = key+u32(1) }
 i = 0
 while i < u32(8) {
  mem[l.unique_at+i] = 2
  i = i+u32(1)
 }
 mem[l.var_at+u32(1)] = key+u32(1)
 mem[l.state_at+STATE_COUNT] = l.cap
 mem[l.state_at+STATE_CREATED] = 19
 mem[l.state_at+STATE_EXCEEDED] = 0
 mode == u32(1) ? {
  // The last permitted probe still finds a reusable node.
  mem[l.unique_at+((start+u32(7))&l.umask)] = 8
  mem[l.var_at+u32(7)] = key
  mem[l.low_at+u32(7)] = 12
  mem[l.high_at+u32(7)] = 14
 } | { }
 mode == u32(2) ? { mem[l.unique_at+start] = l.cap+u32(1) } | { }
 mode == u32(3) ? { mem[l.unique_at+start] = u32(4294967295) } | { }
 mode == u32(4) ? { l.umask = u32(0); mem[l.unique_at] = u32(2) } | { }
 i = 0
 while i < len(mem) { want[i] = mem[i]; i = i+u32(1) }
 want[l.state_at+STATE_CREATED] = 0
 result: u32 = NONE
 mode == u32(1) ? { result = u32(7) } | {
  want[l.state_at+STATE_EXCEEDED] = 1
 }
 assert(cnf_node(l,span(&mem),key,u32(12),u32(14)) == result)
 i = 0
 while i < len(mem) { assert(mem[i] == want[i]); i = i+u32(1) }
}
main: (): i32 {
 start: u32 = 0
 while start < u32(8) {
  collisions: u32 = 0
  while collisions < u32(7) {
   mode: u32 = 0
   while mode < u32(4) {
    case(start,collisions,mode)
    mode = mode+u32(1)
   }
   collisions = collisions+u32(1)
  }
  mode: u32 = 0
  while mode < u32(5) { full_case(start,mode); mode = mode+u32(1) }
  start = start+u32(1)
 }
 0
}
`
	if err := os.WriteFile(filepath.Join(dir, "main.oak"), []byte(source), 0600); err != nil {
		t.Fatal(err)
	}
	c, err := compiler.New().WithPackageDir(dir).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	cpath, bin := filepath.Join(dir, "nodes.c"), filepath.Join(dir, "nodes")
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
	t.Log("checked 264 allocator cases with complete 96-word memory comparison")
}

func TestOakCNFNodesLean(t *testing.T) {
	lake, err := exec.LookPath("lake")
	if err != nil {
		if os.Getenv("OAK_REQUIRE_LRAT_BINDING_LEAN") != "" {
			t.Fatal("lake required for CNF node proof")
		}
		t.Skip("lake unavailable; formal CI requires CNF node proof")
	}
	var contract strings.Builder
	contract.WriteString(`import Oak.CNFNodes
open Oak.CNFEmission Oak.CNFNodes
example (l : Layout) (mem : Array UInt32) (key a b h n remaining : UInt32) (fuel : Nat)
    (running : mem.getD (l.state_at + STATE_EXCEEDED).toNat 0 = 0)
    (slot : mem.getD (l.unique_at + h).toNat 0 = 0)
    (count : mem.getD (l.state_at + STATE_COUNT).toNat 0 = n)
    (room : n < l.cap) (valid : n ≠ NONE) :
    cnf_node.loop1 l mem key a b h NONE remaining (fuel + 2) =
      some (allocate l mem key a b h n, h, n, remaining) :=
  fresh l mem key a b h n remaining fuel running slot count room valid
example (l : Layout) (mem : Array UInt32) (key a b h e remaining : UInt32) (fuel : Nat)
    (running : mem.getD (l.state_at + STATE_EXCEEDED).toNat 0 = 0)
    (slot : mem.getD (l.unique_at + h).toNat 0 = e) (occupied : e ≠ 0)
    (inRange : ¬ e - 1 ≥ l.cap) (valid : e - 1 ≠ NONE) (hit : Matches l mem key a b (e - 1)) :
    cnf_node.loop1 l mem key a b h NONE remaining (fuel + 2) = some (mem, h, e - 1, remaining) :=
  reuse l mem key a b h e remaining fuel running slot occupied inRange valid hit
example (l : Layout) (mem : Array UInt32) (key a b : UInt32)
    (bound : (l.state_at + STATE_EXCEEDED).toNat < mem.size) :
    ∃ out, cnf_node l mem key a b (l.umask.toNat + 2) = some out := by
  simpa using production_terminates l mem key a b 0 bound
example : Oak.CNFGates.Regular ((2147483646 : UInt32) <<< (1 : UInt32)) := fresh_edge 2147483646 2147483647 (by decide) (by decide) (by decide)
example : ¬ Oak.CNFGates.Regular ((2147483647 : UInt32) <<< (1 : UInt32)) := by unfold Oak.CNFGates.Regular; decide +kernel
`)
	names := []string{"stopped", "reuse", "collision", "fresh", "exhausted", "probes_execution", "production", "allocate_size", "allocate_frame", "allocate_readback", "fresh_index", "fresh_edge", "invalid_entry", "probe_exhausted", "loop_terminates", "production_terminates"}
	for _, name := range names {
		fmt.Fprintf(&contract, "#print axioms Oak.CNFNodes.%s\n", name)
	}
	path := filepath.Join(t.TempDir(), "CNFNodesContract.lean")
	if err := os.WriteFile(path, []byte(contract.String()), 0600); err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(t.Context(), 3*time.Minute)
	defer cancel()
	for _, args := range [][]string{{"build", "Oak.CNFNodes"}, {"env", "lean", path}} {
		cmd := exec.CommandContext(ctx, lake, args...)
		cmd.Dir = filepath.Join("spec", "lean")
		out, err := cmd.CombinedOutput()
		if err != nil {
			t.Fatalf("CNF node proof: %v\n%s", err, out)
		}
		if args[0] != "env" {
			continue
		}
		if err := cnfAxiomAudit(string(out), "Oak.CNFNodes", names); err != nil {
			t.Fatalf("%v\n%s", err, out)
		}
	}
}
