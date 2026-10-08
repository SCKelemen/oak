package machine

import (
	"encoding/binary"
	"fmt"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/optir"
)

func TestAArch64SpillMemorySelectorLean(t *testing.T) {
	types := []struct {
		typ   optir.Type
		kind  string
		width uint8
	}{
		{optir.TypeBool, "u8", 1}, {"u8", "u8", 1}, {"i8", "i8", 1}, {"u16", "u16", 2}, {"i16", "i16", 2},
		{"u32", "w32", 4}, {"i32", "w32", 4}, {"u64", "x64", 8}, {"i64", "x64", 8},
	}
	var examples []string
	positive, negative := 0, 0
	for _, tc := range types {
		for _, offset := range []int64{0, int64(tc.width), 16, 248, 256, 4080 - int64(tc.width)} {
			// Obtain the physical offset from the real layout routine, not a test
			// reimplementation of slot alignment. The final slot is the target.
			var abstract []optir.SpillSlot
			for at := int64(0); at <= offset; at += int64(tc.width) {
				abstract = append(abstract, optir.SpillSlot{ID: optir.SpillSlotID(len(abstract) + 1), WidthBytes: tc.width, AlignmentBytes: tc.width})
			}
			slots, _, err := optIRArm64LayoutSpills(abstract)
			if err != nil {
				t.Fatal(err)
			}
			id := abstract[len(abstract)-1].ID
			if slots[id].offset != offset {
				t.Fatalf("layout offset=%d want %d", slots[id].offset, offset)
			}
			for _, regs := range [][2]int{{0, 0}, {0, 9}, {15, 16}, {17, 0}, {30, 30}, {31, 9}} {
				selector := optIRArm64Selector{written: map[int]bool{}, slots: slots}
				if err := selector.storeSpill(id, regs[0], tc.typ, 1); err != nil {
					t.Fatal(err)
				}
				if err := selector.loadSpill(id, regs[1], tc.typ, 1); err != nil {
					t.Fatal(err)
				}
				body, relocs, err := asm.EncodeFunction(fn(selector.items...))
				if err != nil || len(relocs) != 0 || len(body) != 8 {
					t.Fatalf("encode: %v %v len=%d", err, relocs, len(body))
				}
				st, ld := binary.LittleEndian.Uint32(body), binary.LittleEndian.Uint32(body[4:])
				pair := func(store, load uint32) string {
					return fmt.Sprintf("checkPair .%s %d %d %d 0x%08x#32 0x%08x#32", tc.kind, regs[0], regs[1], offset, store, load)
				}
				examples = append(examples, "example : "+pair(st, ld)+" = true := by decide")
				positive++
				// Wrong base register, wrong scaled offset, and swapped load/store.
				for _, bad := range []string{pair(st^(1<<5), ld), pair(st, ld^(1<<10)), pair(ld, st)} {
					examples = append(examples, "example : "+bad+" = false := by decide")
					negative++
				}
				if offset == 0 && regs == [2]int{0, 9} {
					examples = append(examples, fmt.Sprintf("example (s : State) (hs : s.sp.toNat %% 16 = 0 ∧ s.sp.toNat + %d ≤ 2^64) : (step 0x%08x#32 s >>= step 0x%08x#32) = some { s with core := { s.core with pc := s.core.pc + 8, regs := writeReg s.core.regs 9 (normalize .%s (Oak.AArch64BranchExecution.readX s.core.regs 0)) }, mem := storeBytes %d s.mem s.sp.toNat (Oak.AArch64BranchExecution.readX s.core.regs 0) } := by\n  simpa [Kind.bytes] using checked_roundtrip .%s 0 9 0 0x%08x#32 0x%08x#32 s (by decide) (by simpa [Kind.bytes] using hs)", tc.width, st, ld, tc.kind, tc.width, tc.kind, st, ld))
				}
			}
		}
	}
	examples = append(examples, "example : checkPair .x64 0 31 0 0xf90003e0#32 0xf94003ff#32 = false := by decide")
	negative++
	examples = append(examples, "example (s : State) : step 0xf90003e0#32 { s with sp := 1 } = none := by rfl", "example (s : State) : step 0xf9000be0#32 { s with sp := 0xfffffffffffffff0#64 } = none := by simp [step, decode, safe, Kind.bytes]")
	t.Logf("%d spill pairs, %d rejections, 9 universal emitted-byte round trips", positive, negative)
	checkAArch64SelectorLean(t, "AArch64SpillMemory", examples)
}

func TestAArch64SpillMemoryLayoutLean(t *testing.T) {
	var examples []string
	// All four-slot width combinations, preserving the real slot order.
	for code := 0; code < 256; code++ {
		var abstract []optir.SpillSlot
		for i := 0; i < 4; i++ {
			w := uint8(1 << ((code >> (2 * i)) & 3))
			abstract = append(abstract, optir.SpillSlot{ID: optir.SpillSlotID(i + 1), WidthBytes: w, AlignmentBytes: w})
		}
		slots, frame, err := optIRArm64LayoutSpills(abstract)
		if err != nil {
			t.Fatal(err)
		}
		var entries []string
		for _, a := range abstract {
			s := slots[a.ID]
			entries = append(entries, fmt.Sprintf("⟨%d,%d⟩", s.offset, s.width))
		}
		examples = append(examples, fmt.Sprintf("example : layoutValid %d [%s] = true := by decide", frame, strings.Join(entries, ",")))
	}
	for _, bad := range []string{"layoutValid 16 [⟨0,8⟩,⟨4,4⟩]", "layoutValid 16 [⟨1,4⟩]", "layoutValid 16 [⟨16,1⟩]", "layoutValid 17 []", "layoutValid 4096 []", "layoutValid 16 [⟨0,3⟩]"} {
		examples = append(examples, "example : "+bad+" = false := by decide")
	}
	// Frame limit and Go refusal agree with the model's 4080-byte bound.
	var limit []optir.SpillSlot
	for i := 1; i <= 510; i++ {
		limit = append(limit, optir.SpillSlot{ID: optir.SpillSlotID(i), WidthBytes: 8, AlignmentBytes: 8})
	}
	slots, frame, err := optIRArm64LayoutSpills(limit)
	if err != nil || frame != 4080 || slots[510].offset != 4072 {
		t.Fatalf("limit layout: %d %v", frame, err)
	}
	limit = append(limit, optir.SpillSlot{ID: 511, WidthBytes: 8, AlignmentBytes: 8})
	examples = append(examples, "example : layoutValid 4080 [⟨4072,8⟩] = true := by decide", "example : layoutValid 0 [] = true := by decide")
	if _, _, err := optIRArm64LayoutSpills(limit); err == nil {
		t.Fatal("oversized frame accepted")
	}
	checkAArch64SelectorLean(t, "AArch64SpillMemory", examples)
}

// Check transitive proof dependencies, not just the presence of proof text:
// a downstream theorem can inherit an axiom from a shared helper or simp lemma.
func TestAArch64SpillMemoryKernelAxioms(t *testing.T) {
	checkAArch64SelectorLean(t, "AArch64SpillMemory", []string{`
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut checked := 0
  for (name, info) in env.constants.toList do
    if name.toString.startsWith "Oak.AArch64SpillMemory." && info.isTheorem then
      checked := checked + 1
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless ["propext", "Classical.choice", "Quot.sound"].contains axiomName.toString do
          throwError "{name} depends on nonstandard axiom {axiomName}"
  -- There are thirteen public laws, plus generated equation/simp theorems.
  unless checked ≥ 13 do
    throwError "spill-memory axiom audit did not find all public laws"
`}, "Lean")
}
