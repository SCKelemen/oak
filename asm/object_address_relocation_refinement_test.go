package asm

import (
	"encoding/binary"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

const (
	testADRPX9 = uint32(0x90000009)
	testADDX9  = uint32(0x91000129)
)

func TestAArch64ADRL21PatchBoundaries(t *testing.T) {
	const maxUint64 = ^uint64(0)
	tests := []struct {
		name          string
		adrp, add     uint32
		place, target uint64
		want          bool
	}{
		{name: "same page and low twelve", adrp: testADRPX9, add: testADDX9, place: 0x10004, target: 0x10abc, want: true},
		{name: "positive page endpoint", adrp: testADRPX9, add: testADDX9, place: 0, target: ((1<<20)-1)<<12 | 0xfff, want: true},
		{name: "negative page endpoint", adrp: testADRPX9, add: testADDX9, place: 1 << 32, target: 0xabc, want: true},
		{name: "highest complete pair", adrp: testADRPX9, add: testADDX9, place: maxUint64 - 7, target: maxUint64, want: true},
		{name: "above positive page endpoint", adrp: testADRPX9, add: testADDX9, place: 0, target: 1 << 32},
		{name: "below negative page endpoint", adrp: testADRPX9, add: testADDX9, place: (1 << 32) + 0x1000, target: 0},
		{name: "uint64 place must not narrow", adrp: testADRPX9, add: testADDX9, place: maxUint64 - 3, target: 0},
		{name: "pair address must not wrap", adrp: testADRPX9, add: testADDX9, place: maxUint64 - 3, target: maxUint64},
		{name: "uint64 target must not narrow", adrp: testADRPX9, add: testADDX9, place: 0, target: maxUint64},
		{name: "misaligned instruction place", adrp: testADRPX9, add: testADDX9, place: 2, target: 0xabc},
		{name: "not adrp", adrp: 0x10000009, add: testADDX9, place: 0, target: 0xabc},
		{name: "not add immediate", adrp: testADRPX9, add: 0xd1000129, place: 0, target: 0xabc},
		{name: "shifted add immediate", adrp: testADRPX9, add: testADDX9 | 1<<22, place: 0, target: 0xabc},
		{name: "different add base", adrp: testADRPX9, add: testADDX9 ^ 1<<5, place: 0, target: 0xabc},
		{name: "different add destination", adrp: testADRPX9, add: testADDX9 ^ 1, place: 0, target: 0xabc},
		{name: "register thirty one", adrp: 0x9000001f, add: 0x910003ff, place: 0, target: 0xabc},
	}
	leanExamples := make([]string, 0, len(tests))
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			patched, err := patchAArch64ADRL21(test.adrp, test.add, test.place, test.target)
			leanResult := "none"
			if err == nil {
				leanResult = fmt.Sprintf("some (0x%08x#32, 0x%08x#32)", patched.adrp, patched.add)
			}
			leanExamples = append(leanExamples, fmt.Sprintf(
				"example : relocateADRL 0x%08x#32 0x%08x#32 %d %d = %s := by decide",
				test.adrp, test.add, test.place, test.target, leanResult))
			if !test.want {
				if err == nil {
					t.Fatalf("patchAArch64ADRL21 accepted %#08x/%#08x as %#08x/%#08x", test.adrp, test.add, patched.adrp, patched.add)
				}
				if patched != (aarch64ADRL21Patch{}) {
					t.Fatalf("refusal returned partial patch %+v", patched)
				}
				return
			}
			if err != nil {
				t.Fatal(err)
			}
			if patched.adrp&^aarch64ADRPImmediateMask != test.adrp&^aarch64ADRPImmediateMask {
				t.Fatalf("ADRP fixed/register fields changed: %#08x -> %#08x", test.adrp, patched.adrp)
			}
			if patched.add&^aarch64ADDImm12Mask != test.add&^aarch64ADDImm12Mask {
				t.Fatalf("ADD fixed/register fields changed: %#08x -> %#08x", test.add, patched.add)
			}
			reached, ok := decodePatchedAArch64ADRL21Target(patched.adrp, patched.add, test.place)
			if !ok || reached != test.target {
				t.Fatalf("patched pair reaches (%#x, %v), want %#x", reached, ok, test.target)
			}
		})
	}

	leanPath := filepath.Join(t.TempDir(), "AArch64AddressRelocationProductionPins.lean")
	leanSource := "import Oak.AArch64AddressRelocation\n\n" +
		"namespace Oak.AArch64AddressRelocation\n\n" +
		strings.Join(leanExamples, "\n") +
		"\n\nend Oak.AArch64AddressRelocation\n"
	if err := os.WriteFile(leanPath, []byte(leanSource), 0o600); err != nil {
		t.Fatal(err)
	}
	lake, err := exec.LookPath("lake")
	if err != nil {
		t.Skip("lake not on PATH; the formal workflow runs this kernel oracle")
	}
	cmd := exec.Command(lake, "env", "lean", leanPath)
	cmd.Dir = filepath.Join("..", "spec", "lean")
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("kernel-checking ADRL21 production pins: %v\n%s\n--- source ---\n%s", err, out, leanSource)
	}
}

func TestResolveRelocationsADRL21RefusalDoesNotMutate(t *testing.T) {
	tests := []struct {
		name      string
		adrp, add uint32
		textAddr  uint64
		offset    int64
		target    uint64
	}{
		{name: "place addition overflow", adrp: testADRPX9, add: testADDX9, textAddr: ^uint64(0) - 3, offset: 4},
		{name: "pair address overflow", adrp: testADRPX9, add: testADDX9, textAddr: ^uint64(0) - 3, target: ^uint64(0)},
		{name: "address narrowing wrap", adrp: testADRPX9, add: testADDX9, textAddr: ^uint64(0) - 3, target: 0},
		{name: "malformed pair", adrp: testADRPX9, add: testADDX9 ^ 1, target: 0xabc},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			text := make([]byte, 12)
			binary.LittleEndian.PutUint32(text[test.offset:], test.adrp)
			binary.LittleEndian.PutUint32(text[test.offset+4:], test.add)
			before := append([]byte(nil), text...)
			layout := &textLayout{
				text: text,
				relocs: []placedReloc{{
					offset: test.offset,
					kind:   "adrl21",
					symbol: "target",
				}},
			}
			if err := resolveRelocations(layout, test.textAddr, map[string]uint64{"target": test.target}); err == nil {
				t.Fatal("resolveRelocations accepted an invalid adrl21")
			}
			if string(layout.text) != string(before) {
				t.Fatalf("resolveRelocations mutated ADRL21 text on refusal: %x -> %x", before, layout.text)
			}
		})
	}
}
