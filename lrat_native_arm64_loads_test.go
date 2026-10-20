package main

import (
	"fmt"
	"strings"
	"testing"
)

// The supplied words come from adjacent instructions in the linked header.
func lratARM64HeaderLoadContract(t *testing.T, load, call uint32) string {
	t.Helper()
	if load&0xffe0ffff != 0xb8605a60 {
		t.Fatalf("unsupported allocation argument load: %#x", load)
	}
	var c strings.Builder
	fmt.Fprintf(&c, `
section
open Oak.LRATARM64HeaderLoads Oak.LRATARM64Bytes
example (mem : Oak.AArch64SpillMemory.Memory) (s : State) (words : Array UInt32) (fuel : Nat)
 (hr : Represents mem (s.regs 19).toNat words)
 (hi : index %d#32 s < words.size)
 (he : (s.regs 19).toNat + words.size * 4 ≤ 2^64) :
 (loadAlloc %d#32 %d#32 mem s).map (fun out => out.regs 0) =
 (Oak.LRATBounds.lrat_alloc_fits (words.getD (index %d#32 s) 0) fuel).map bit :=
 allocation_refines _ _ _ _ _ _ (by decide) (by decide) hr hi he
end
`, load, load, call, load)
	// Concrete byte memories exercise zero extension, high-bit rejection and
	// byte order through the complete load/call/body composition.
	for _, tc := range []struct {
		mem  string
		want int
	}{
		{"fun _ => 0", 1},
		{"fun _ => 255", 0},
		{"fun a => if a = 3 then 64 else 0", 0}, // LE 0x40000000
		{"fun a => if a = 0 then 64 else 0", 1}, // LE 0x00000040
	} {
		fmt.Fprintf(&c, "example : (Oak.LRATARM64HeaderLoads.loadAlloc %d#32 %d#32 (%s) ⟨fun _ => 0,0,0,⟨false,false,false,false⟩⟩).map (fun out => out.regs 0) = some %d := by decide\n", load, call, tc.mem, tc.want)
	}
	// Reject changed width, extension, scale, base and destination.
	for _, mask := range []uint32{0x40000000, 0x8000, 0x1000, 0x20, 1} {
		fmt.Fprintf(&c, "example (mem : Oak.AArch64SpillMemory.Memory) (s : Oak.LRATARM64Bytes.State) : Oak.LRATARM64HeaderLoads.load %d#32 mem s = none := by simp [Oak.LRATARM64HeaderLoads.load]\n", load^mask)
	}
	fmt.Fprintf(&c, "example : (Oak.LRATARM64HeaderLoads.load %d#32 (fun _ => 0) ⟨fun r => if r = 19 then 18446744073709551615 else 0,0,0,⟨false,false,false,false⟩⟩).isNone = true := by decide\n", load)
	return c.String()
}
