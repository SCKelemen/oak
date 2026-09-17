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

// decodeAArch64Branch26TargetForTest is an independent test oracle for the signed,
// scaled imm26 field. The explicit overflow checks keep the near-MaxUint64
// cases meaningful instead of letting the oracle reproduce address wrapping.
func decodeAArch64Branch26TargetForTest(word uint32, place uint64) (uint64, bool) {
	words := int64(word & aarch64Branch26Immediate)
	if words&(1<<25) != 0 {
		words -= 1 << 26
	}
	delta := words * 4
	if delta >= 0 {
		bytes := uint64(delta)
		if place > ^uint64(0)-bytes {
			return 0, false
		}
		return place + bytes, true
	}
	bytes := uint64(-delta)
	if bytes > place {
		return 0, false
	}
	return place - bytes, true
}

func leanBranch26Kind(kind string) (string, bool) {
	switch kind {
	case "call26":
		return ".call", true
	case "jump26", "branch26":
		return ".jump", true
	default:
		return "", false
	}
}

// ObjectRelocation.lean specifies the exact signed-range, alignment, opcode,
// patch, and decode core used by the executable writer. Each Go result below
// is rendered into a temporary Lean example and checked by Lean's kernel, so
// neither a stale list of handwritten examples nor a second Go implementation
// can silently bless drift between the production decision and the model.
func TestAArch64Branch26RelocationMatchesLean(t *testing.T) {
	const maxUint64 = ^uint64(0)
	tests := []struct {
		name           string
		kind           string
		original       uint32
		place, target  uint64
		wantSuccessful bool
	}{
		{name: "exact negative endpoint", kind: "jump26", original: 0x17ffffff, place: 1 << 27, target: 0, wantSuccessful: true},
		{name: "exact positive endpoint", kind: "call26", original: 0x97ffffff, place: 0, target: (1 << 27) - 4, wantSuccessful: true},
		{name: "one word below negative endpoint", kind: "jump26", original: 0x14000000, place: (1 << 27) + 4, target: 0},
		{name: "one word above positive endpoint", kind: "call26", original: 0x94000000, place: 0, target: 1 << 27},
		{name: "unaligned target", kind: "call26", original: 0x94000000, place: 0x10000, target: 0x10002},
		{name: "jointly misaligned addresses", kind: "jump26", original: 0x14000000, place: 1, target: 5},
		{name: "call on B opcode", kind: "call26", original: 0x14000000, place: 0x10000, target: 0x1000c},
		{name: "jump on BL opcode", kind: "jump26", original: 0x94000000, place: 0x10000, target: 0x1000c},
		{name: "unknown kind", kind: "future26", original: 0x94000000, place: 0x10000, target: 0x1000c},
		{name: "forward call", kind: "call26", original: 0x97ffffff, place: 0x10000, target: 0x1000c, wantSuccessful: true},
		{name: "backward jump", kind: "jump26", original: 0x17ffffff, place: 0x1000c, target: 0x10000, wantSuccessful: true},
		{name: "zero legacy branch", kind: "branch26", original: 0x15ffffff, place: 0x10000, target: 0x10000, wantSuccessful: true},
		{name: "near max forward", kind: "call26", original: 0x97ffffff, place: maxUint64 - 15, target: maxUint64 - 3, wantSuccessful: true},
		{name: "near max backward", kind: "jump26", original: 0x17ffffff, place: maxUint64 - 3, target: maxUint64 - 15, wantSuccessful: true},
		{name: "near max zero", kind: "call26", original: 0x97ffffff, place: maxUint64 - 3, target: maxUint64 - 3, wantSuccessful: true},
		{name: "uint64 subtraction must not wrap positive", kind: "call26", original: 0x94000000, place: 0, target: maxUint64 - 3},
		{name: "uint64 subtraction must not wrap negative", kind: "jump26", original: 0x14000000, place: maxUint64 - 3, target: 0},
	}

	var leanExamples []string
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			patched, err := patchAArch64Branch26(test.kind, test.original, test.place, test.target)
			if test.wantSuccessful {
				if err != nil {
					t.Fatalf("patchAArch64Branch26: %v", err)
				}
				if patched&aarch64Branch26OpcodeMask != test.original&aarch64Branch26OpcodeMask {
					t.Fatalf("patched word %#08x changed opcode %#08x", patched, test.original&aarch64Branch26OpcodeMask)
				}
				target, representable := decodeAArch64Branch26TargetForTest(patched, test.place)
				if !representable || target != test.target {
					t.Fatalf("patched word %#08x reaches (%#x, %v), want %#x", patched, target, representable, test.target)
				}
			} else if err == nil {
				t.Fatalf("patchAArch64Branch26 returned %#08x, want refusal", patched)
			}

			kind, known := leanBranch26Kind(test.kind)
			if !known {
				leanExamples = append(leanExamples, fmt.Sprintf(
					"example : branch26Kind? %q = none := by decide", test.kind))
				return
			}
			result := "none"
			if err == nil {
				result = fmt.Sprintf("some 0x%08x#32", patched)
			}
			leanExamples = append(leanExamples, fmt.Sprintf(
				"example : relocateBranch26 %s 0x%08x#32 %d %d = %s := by decide",
				kind, test.original, test.place, test.target, result))
		})
	}

	leanPath := filepath.Join(t.TempDir(), "ObjectRelocationProductionPins.lean")
	leanSource := "import Oak.ObjectRelocation\n\nnamespace Oak.ObjectRelocation\n\n" +
		strings.Join(leanExamples, "\n") + "\n\nend Oak.ObjectRelocation\n"
	if err := os.WriteFile(leanPath, []byte(leanSource), 0o600); err != nil {
		t.Fatal(err)
	}
	lake, err := exec.LookPath("lake")
	if err != nil {
		t.Skip("lake not on PATH; the formal workflow runs this kernel oracle")
	}
	buildLeanImports(t, lake, leanPath)
	cmd := exec.Command(lake, "env", "lean", leanPath)
	cmd.Dir = filepath.Join("..", "spec", "lean")
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("kernel-checking production relocation pins: %v\n%s\n--- source ---\n%s", err, out, leanSource)
	}
}

func TestResolveRelocationsRejectsOverflowingAddressesAndOffsets(t *testing.T) {
	maxInt64 := int64(^uint64(0) >> 1)
	tests := []struct {
		name     string
		textAddr uint64
		offset   int64
		kind     string
		textLen  int
	}{
		{name: "branch relocation offset MaxInt64", offset: maxInt64, kind: "call26", textLen: 8},
		{name: "paired relocation offset MaxInt64", offset: maxInt64, kind: "adrl21", textLen: 8},
		{name: "branch place addition overflows", textAddr: ^uint64(0) - 3, offset: 4, kind: "call26", textLen: 8},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			text := make([]byte, test.textLen)
			binary.LittleEndian.PutUint32(text[4:], aarch64BLOpcode)
			before := append([]byte(nil), text...)
			layout := &textLayout{
				text:   text,
				relocs: []placedReloc{{offset: test.offset, kind: test.kind, symbol: "target"}},
			}
			err := resolveRelocations(layout, test.textAddr, map[string]uint64{"target": 0})
			if err == nil {
				t.Fatal("resolveRelocations accepted an overflowing address or offset")
			}
			if string(layout.text) != string(before) {
				t.Fatalf("resolveRelocations mutated text on refusal: %x -> %x", before, layout.text)
			}
		})
	}
}
