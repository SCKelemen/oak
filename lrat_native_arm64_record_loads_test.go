package main

import (
	"fmt"
	"strings"
	"testing"
)

// Pin the three adjacent argument instructions from the linked record caller.
func lratARM64RecordLoadContract(t *testing.T, load, start, limit, call uint32) string {
	t.Helper()
	if load&0xffe0ffff != 0xb8605a61 || start != 0x52800100 || limit != 0x2a1403e2 {
		t.Fatalf("unsupported record argument preparation: %#x %#x %#x", load, start, limit)
	}
	var c strings.Builder
	fmt.Fprintf(&c, `
section
open Oak.LRATARM64RecordLoads Oak.LRATARM64Bytes
open Oak.LRATARM64HeaderLoads (Represents index)
example (mem : Oak.AArch64SpillMemory.Memory) (s : State) (words : Array UInt32) (fuel : Nat)
 (hr : Represents mem (s.regs 19).toNat words)
 (hi : index %d#32 s < words.size)
 (he : (s.regs 19).toNat + words.size * 4 ≤ 2^64)
 (hx : index %d#32 s = 3)
 (hl : UInt32.ofBitVec (Oak.AArch64BitwiseFunction.readW s.regs 20) = UInt32.ofNat words.size) :
 (recordFits %d#32 %d#32 %d#32 %d#32 mem s).map (fun out => out.regs 0) =
 (Oak.LRATBounds.lrat_fits 8 (words.getD 3 0) (UInt32.ofNat words.size) fuel).map bit :=
 record_refines _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) hr hi he hx hl
end
`, load, load, load, start, limit, call)
	// Exercise the inclusive count boundary, the start bound, and high-bit loads.
	for _, tc := range []struct {
		count        uint32
		length, want int
	}{
		{0, 8, 1}, {4, 12, 1}, {5, 12, 0}, {0, 7, 0}, {0x80000000, 12, 0}, {0xffffffff, 12, 0},
	} {
		fmt.Fprintf(&c, "example : (Oak.LRATARM64RecordLoads.recordFits %d#32 %d#32 %d#32 %d#32 (fun a => BitVec.ofNat 8 ((%d / 2^(a*8)) %% 256)) ⟨fun r => if r = 20 then %d else 0,0,0,⟨false,false,false,false⟩⟩).map (fun out => out.regs 0) = some %d := by decide\n", load, start, limit, call, tc.count, tc.length, tc.want)
	}
	for _, bad := range [][3]uint32{
		{load ^ 0x40000000, start, limit}, {load ^ 0x8000, start, limit},
		{load ^ 0x1000, start, limit}, {load ^ 0x20, start, limit}, {load ^ 1, start, limit},
		{load, start ^ 0x20, limit}, {load, start, limit ^ 0x10000},
	} {
		fmt.Fprintf(&c, "example (mem : Oak.AArch64SpillMemory.Memory) (s : Oak.LRATARM64Bytes.State) : Oak.LRATARM64RecordLoads.prepare %d#32 %d#32 %d#32 mem s = none := by simp [Oak.LRATARM64RecordLoads.prepare]\n", bad[0], bad[1], bad[2])
	}
	fmt.Fprintf(&c, "example : (Oak.LRATARM64RecordLoads.prepare %d#32 %d#32 %d#32 (fun _ => 0) ⟨fun r => if r = 19 then 18446744073709551615 else 0,0,0,⟨false,false,false,false⟩⟩).isNone = true := by decide\n", load, start, limit)
	return c.String()
}
