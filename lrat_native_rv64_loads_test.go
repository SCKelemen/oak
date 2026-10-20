package main

import (
	"fmt"
	"strings"
	"testing"
)

func lratRV64HeaderLoadContract(t *testing.T, load, move, upper, lower uint32, profile string) string {
	t.Helper()
	if load&0xfff07fff != 0x2503 || move != 0x00028913 {
		t.Fatalf("unsupported RV64 allocation preparation: %#x %#x", load, move)
	}
	pair := fmt.Sprintf("(%d#32,%d#32)", upper, lower)
	var c strings.Builder
	fmt.Fprintf(&c, `
section
open Oak.RiscVCallExecution Oak.LRATHeaderMemory Oak.LRATRV64HeaderLoads
example (mem : Oak.AArch64SpillMemory.Memory) (s : State) (base i : Nat) (words : Array UInt32) (fuel : Nat)
 (ha : address %d#32 s = base + i * 4)
 (hr : Represents mem base words) (hi : i < words.size)
 (he : base + words.size * 4 ≤ 2^64) :
 (%s.loadAlloc %d#32 %s mem s).map (fun out => read out 10) =
 (Oak.LRATBounds.lrat_alloc_fits (words.getD i 0) fuel).map Oak.LRATRV64Bytes.bit :=
 %s.allocation_refines _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) ha hr hi he
end
`, load, profile, load, pair, profile)
	for _, tc := range []struct {
		mem  string
		want int
	}{
		{"fun _ => 0", 1}, {"fun _ => 255", 0},
		{"fun a => if a = 3 then 128 else 0", 0},
		{"fun a => if a = 0 then 128 else 0", 1},
	} {
		fmt.Fprintf(&c, "example : (Oak.LRATRV64HeaderLoads.%s.loadAlloc %d#32 %s (%s) ⟨0,fun _ => 0⟩).map (fun out => Oak.RiscVCallExecution.read out 10) = some %d := by decide\n", profile, load, pair, tc.mem, tc.want)
	}
	fmt.Fprintf(&c, "example : (Oak.LRATRV64HeaderLoads.load %d#32 (fun a => if a = 3 then 128 else 0) ⟨0,fun _ => 0⟩).map (fun out => Oak.RiscVCallExecution.read out 10) = some 18446744071562067968 := by decide\n", load)
	// LWU, LD, nonzero displacement and a different destination are excluded.
	for _, mask := range []uint32{0x4000, 0x1000, 0x100000, 0x80} {
		fmt.Fprintf(&c, "example (mem : Oak.AArch64SpillMemory.Memory) (s : Oak.RiscVCallExecution.State) : Oak.LRATRV64HeaderLoads.load %d#32 mem s = none := by simp [Oak.LRATRV64HeaderLoads.load]\n", load^mask)
	}
	fmt.Fprintf(&c, "example : (Oak.LRATRV64HeaderLoads.load %d#32 (fun _ => 0) ⟨0,fun _ => 18446744073709551615⟩).isNone = true := by decide\n", load)
	return c.String()
}
