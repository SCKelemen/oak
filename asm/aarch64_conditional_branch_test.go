package asm

import (
	"bytes"
	"debug/elf"
	"encoding/binary"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

var aarch64Cond19Kinds = []string{"bcond", "cbz32", "cbz64", "cbnz32", "cbnz64"}
var aarch64Cond19Conditions = []string{"eq", "ne", "cs", "cc", "mi", "pl", "vs", "vc", "hi", "ls", "ge", "lt", "gt", "le", "al", "nv"}

func aarch64Cond19Instruction(kind string, low int) Instruction {
	if kind == "bcond" {
		return Instruction{Mnemonic: "b.", Cond: aarch64Cond19Conditions[low], Operands: []Operand{Symbol{Name: "target"}}}
	}
	class := ClassW
	if strings.HasSuffix(kind, "64") {
		class = ClassX
	}
	return Instruction{Mnemonic: strings.TrimSuffix(strings.TrimSuffix(kind, "32"), "64"),
		Operands: []Operand{Register{Class: class, Num: low, Lane: -1}, Symbol{Name: "target"}}}
}

// This oracle sign-extends the extracted field arithmetically, independently
// of both production magnitude subtraction and its shift-based decoder.
func aarch64Cond19Delta(word uint32) int64 {
	imm := int64(word >> 5 & 0x7ffff)
	if imm >= 1<<18 {
		imm -= 1 << 19
	}
	return imm * 4
}

func TestAArch64ConditionalBranchLeanRows(t *testing.T) {
	data, err := os.ReadFile(filepath.Join("..", "spec", "lean", "Oak", "AArch64ConditionalBranch.lean"))
	if err != nil {
		t.Fatal(err)
	}
	var want []string
	for i, name := range []string{"B_only_condbranch", "CBZ_32_compbranch", "CBZ_64_compbranch", "CBNZ_32_compbranch", "CBNZ_64_compbranch"} {
		found := 0
		for _, row := range isaEncodings {
			if row.Name != name {
				continue
			}
			found++
			var fields []string
			for _, f := range row.Fields {
				fields = append(fields, fmt.Sprintf("⟨%q, %d, %d⟩", f.Name, f.Hi, f.Width))
			}
			want = append(want, fmt.Sprintf("def %s : Encoding := ⟨%q, %q, 0x%08x#32, 0x%08x#32, [%s]⟩",
				aarch64Cond19Kinds[i], row.Name, row.Mnemonic, row.Value, row.Mask, strings.Join(fields, ", ")))
			if len(row.Forms) != 1 || len(row.Forms[0].Operands) != 2 {
				t.Fatalf("unexpected operand forms: %+v", row)
			}
			label := row.Forms[0].Operands[1]
			if label.Kind != "label" || strings.Join(label.Fields, ":") != "imm19" ||
				!label.HasRange || label.Min != -(1<<20) || label.Max != (1<<20)-1 || label.Scale != 4 {
				t.Fatalf("range/scale drift: %+v", label)
			}
		}
		if found != 1 {
			t.Fatalf("%s: %d generated rows", name, found)
		}
	}
	start := strings.Index(string(data), "-- OAK-A64-COND19-ENC-BEGIN")
	end := strings.Index(string(data), "-- OAK-A64-COND19-ENC-END")
	if start < 0 || end <= start {
		t.Fatal("missing Lean row block")
	}
	block := strings.SplitN(string(data)[start:end], "\n", 2)[1]
	if strings.TrimSpace(block) != strings.Join(want, "\n") {
		t.Fatalf("Lean row block drifted from generated Arm table:\n%s", block)
	}
}

func checkAArch64Cond19Lean(t *testing.T, examples []string) {
	t.Helper()
	checkAArch64BranchLean(t, "AArch64ConditionalBranch", examples)
}

func checkAArch64BranchLean(t *testing.T, module string, examples []string) {
	t.Helper()
	lake, err := exec.LookPath("lake")
	if err != nil {
		if os.Getenv("OAK_REQUIRE_ARM64_COND19_LEAN") != "" {
			t.Fatal("lake required for ARM64 conditional branch production correspondence")
		}
		t.Skip("lake not on PATH; formal workflow requires this oracle")
	}
	source := "import Oak." + module + "\nopen Oak." + module + "\n" + strings.Join(examples, "\n") + "\n"
	path := filepath.Join(t.TempDir(), "AArch64ConditionalProductionPins.lean")
	if err := os.WriteFile(path, []byte(source), 0600); err != nil {
		t.Fatal(err)
	}
	buildLeanImports(t, lake, path)
	cmd := exec.Command(lake, "env", "lean", path)
	cmd.Dir = filepath.Join("..", "spec", "lean")
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("ARM64 conditional production correspondence: %v\n%s", err, out)
	}
	t.Logf("Lean checked %d production decisions/byte streams", len(examples))
}

func TestAArch64ConditionalLocalMatchesLean(t *testing.T) {
	const max = int64(^uint64(0) >> 1)
	const min = -max - 1
	cases := []struct {
		pc, target int64
		accept     bool
	}{
		{0, 0, true}, {4096, 4124, true}, {4096, 4092, true},
		{1 << 20, 0, true}, {0, (1 << 20) - 4, true},
		{(1 << 20) + 4, 0, false}, {0, 1 << 20, false},
		{0, 2, false}, {2, 4, false}, {1, 5, false}, {2, 6, false}, {3, 7, false},
		{max - 7, max - 3, true}, {min, min + 4, true},
		{min + 4, max - 3, false}, {max - 3, min + 4, false},
	}
	var examples []string
	for _, kind := range aarch64Cond19Kinds {
		lows := 32
		if kind == "bcond" {
			lows = 16
		}
		for low := 0; low < lows; low++ {
			instr := aarch64Cond19Instruction(kind, low)
			for _, tc := range cases {
				word, rel, err := EncodeInstruction(instr, tc.pc, map[string]int64{"target": tc.target})
				if (err == nil) != tc.accept || rel != nil {
					t.Fatalf("%s/%d (%d,%d): %#x %v %v; accept=%v", kind, low, tc.pc, tc.target, word, rel, err, tc.accept)
				}
				result := "none"
				if err == nil {
					if aarch64Cond19Delta(word) != tc.target-tc.pc || int(word&31) != low {
						t.Fatalf("wrong immediate/operand: %#x", word)
					}
					result = fmt.Sprintf("some 0x%08x#32", word)
				} else if word != 0 {
					t.Fatalf("refused local branch returned %#x", word)
				}
				examples = append(examples, fmt.Sprintf("example : localBranch .%s %d#5 (%d : Int) (%d : Int) = %s := by decide", kind, low, tc.pc, tc.target, result))
			}
			word, rel, err := EncodeInstruction(instr, 0, nil)
			if err != nil || rel == nil || rel.Kind != "condbr19" || rel.Symbol != "target" || aarch64Cond19Delta(word) != 0 {
				t.Fatalf("external %s/%d: %#x %+v %v", kind, low, word, rel, err)
			}
		}
	}
	// Bind the actual function writer's little-endian output to Lean as well.
	fn := &Function{Name: "branches", Arch: ArchArm64, Items: []Item{Label{Name: "target"}}}
	for _, kind := range aarch64Cond19Kinds {
		fn.Items = append(fn.Items, aarch64Cond19Instruction(kind, 1))
	}
	code, rels, err := EncodeFunction(fn)
	if err != nil || len(rels) != 0 || len(code) != 20 {
		t.Fatalf("function: %x %v %v", code, rels, err)
	}
	for i, kind := range aarch64Cond19Kinds {
		b := code[i*4 : i*4+4]
		examples = append(examples, fmt.Sprintf("example : wordBytes (encode .%s 1 (BitVec.ofInt 19 (%d))) = [%d#8, %d#8, %d#8, %d#8] := by decide", kind, -i, b[0], b[1], b[2], b[3]))
	}
	checkAArch64Cond19Lean(t, examples)
}

func TestAArch64ConditionalRelocationMatchesLean(t *testing.T) {
	const max = ^uint64(0)
	cases := []struct {
		place, target uint64
		accept        bool
	}{
		{0, 0, true}, {4096, 4124, true}, {4096, 4092, true},
		{1 << 20, 0, true}, {0, (1 << 20) - 4, true},
		{(1 << 20) + 4, 0, false}, {0, 1 << 20, false},
		{0, 2, false}, {1, 5, false}, {2, 6, false}, {3, 7, false},
		{max - 7, max - 3, true}, {max - 3, max - 7, true}, {max - 3, max - 3, true},
		{0, max - 3, false}, {max - 3, 0, false},
		{(1 << 63) - 4, 1 << 63, true}, {1 << 63, (1 << 63) - 4, true},
	}
	var examples []string
	for _, kind := range aarch64Cond19Kinds {
		low := 31
		if kind == "bcond" {
			low = 15
		}
		base, _, err := EncodeInstruction(aarch64Cond19Instruction(kind, low), 0, nil)
		if err != nil {
			t.Fatal(err)
		}
		// Dirty immediates exercise replacement, not merely OR-ing fresh fields.
		for _, old := range []uint32{0, 0x00555540, 0x00ffffe0} {
			original := base | old
			for _, tc := range cases {
				word, err := patchAArch64CondBranch19(original, tc.place, tc.target)
				if (err == nil) != tc.accept {
					t.Fatalf("%s (%#x,%#x): %#x %v; accept=%v", kind, tc.place, tc.target, word, err, tc.accept)
				}
				result := "none"
				if err == nil {
					if word&0xff00001f != original&0xff00001f {
						t.Fatalf("changed fixed fields: %#x -> %#x", original, word)
					}
					delta := aarch64Cond19Delta(word)
					if delta >= 0 && (tc.target < tc.place || tc.target-tc.place != uint64(delta)) ||
						delta < 0 && (tc.target > tc.place || tc.place-tc.target != uint64(-delta)) {
						t.Fatalf("incorrect decoded target: %#x", word)
					}
					result = fmt.Sprintf("some 0x%08x#32", word)
				} else if word != 0 {
					t.Fatalf("refusal returned nonzero word: %#x", word)
				}
				examples = append(examples, fmt.Sprintf("example : relocate 0x%08x#32 %d %d = %s := by decide", original, tc.place, tc.target, result))
			}
		}
	}
	// Mutate every fixed opcode bit in every admitted form; mutation can select
	// another admitted form (sf/op), which is valid and must match the model.
	for _, base := range []uint32{0x54000000, 0x34000000, 0xb4000000, 0x35000000, 0xb5000000} {
		for bit := uint(24); bit < 32; bit++ {
			original := base ^ (1 << bit)
			word, err := patchAArch64CondBranch19(original, 4096, 4100)
			result := "none"
			if err == nil {
				result = fmt.Sprintf("some 0x%08x#32", word)
			}
			examples = append(examples, fmt.Sprintf("example : relocate 0x%08x#32 4096 4100 = %s := by decide", original, result))
		}
	}
	for _, word := range []uint32{0, 0xffffffff, 0x54000010, 0x14000000, 0x94000000, 0x36000000, 0x58000000} {
		if patched, err := patchAArch64CondBranch19(word, 0, 4); err == nil || patched != 0 {
			t.Fatalf("admitted non-conditional word %#x", word)
		}
		examples = append(examples, fmt.Sprintf("example : relocate 0x%08x#32 0 4 = none := by decide", word))
	}
	checkAArch64Cond19Lean(t, examples)
}

func TestAArch64ConditionalRelocationRefusalPreservesText(t *testing.T) {
	for _, tc := range []struct {
		name         string
		word         uint32
		base, target uint64
		offset       int64
	}{
		{"wrapped positive", 0x54000000, 0, ^uint64(0) - 3, 0},
		{"wrapped negative", 0xb5000000, ^uint64(0) - 3, 0, 0},
		{"place addition overflow", 0x34000000, ^uint64(0) - 3, 0, 4},
		{"joint alignment", 0x35000000, 1, 5, 0},
		{"unrelated opcode", 0xd503201f, 0, 4, 0},
		{"BC.cond", 0x54000010, 0, 4, 0},
		{"out of range", 0x54000000, 0, 1 << 20, 0},
	} {
		t.Run(tc.name, func(t *testing.T) {
			data := bytes.Repeat([]byte{0xa5}, 12)
			binary.LittleEndian.PutUint32(data[tc.offset:], tc.word)
			before := append([]byte(nil), data...)
			layout := &textLayout{text: data, relocs: []placedReloc{{offset: tc.offset, kind: "condbr19", symbol: "target"}}}
			if err := resolveRelocations(layout, tc.base, map[string]uint64{"target": tc.target}); err == nil {
				t.Fatal("accepted invalid relocation")
			}
			if !bytes.Equal(before, layout.text) {
				t.Fatalf("mutated refused relocation: %x -> %x", before, layout.text)
			}
		})
	}
}

func TestAArch64ConditionalExecutableTargets(t *testing.T) {
	for _, kind := range aarch64Cond19Kinds {
		branch := &Function{Name: "source", Arch: ArchArm64, Items: []Item{aarch64Cond19Instruction(kind, 1)}}
		target := &Function{Name: "target", Arch: ArchArm64, Items: []Item{Instruction{Mnemonic: "ret"}}}
		for _, fns := range [][]*Function{{branch, target}, {target, branch}} {
			encoded, err := EncodeFunctions(fns, func(s string) string { return s })
			if err != nil {
				t.Fatal(err)
			}
			image, err := WriteExecutable(encoded, ExecutableOptions{OS: OSFreestanding, Arch: ArchArm64, Entry: "source"})
			if err != nil {
				t.Fatal(err)
			}
			f, err := elf.NewFile(bytes.NewReader(image))
			if err != nil {
				t.Fatal(err)
			}
			syms, err := f.Symbols()
			if err != nil {
				t.Fatal(err)
			}
			addr := map[string]uint64{}
			for _, s := range syms {
				addr[s.Name] = s.Value
			}
			sec := f.Section(".text")
			data, err := sec.Data()
			if err != nil {
				t.Fatal(err)
			}
			word := binary.LittleEndian.Uint32(data[addr["source"]-sec.Addr:])
			if int64(addr["source"])+aarch64Cond19Delta(word) != int64(addr["target"]) {
				t.Fatalf("%s executable branch misses target: %#x", kind, word)
			}
		}
	}
}

func TestAArch64LiteralDoesNotUseConditionalRelocation(t *testing.T) {
	instr := Instruction{Mnemonic: "ldr", Operands: []Operand{Register{Class: ClassX, Num: 0, Lane: -1}, Symbol{Name: "target"}}}
	if word, rel, err := EncodeInstruction(instr, 0, nil); err == nil || word != 0 || rel != nil {
		t.Fatalf("literal load mislabeled as conditional relocation: %#x %+v %v", word, rel, err)
	}
	if _, rel, err := EncodeInstruction(instr, 0, map[string]int64{"target": 4}); err != nil || rel != nil {
		t.Fatalf("local literal load unexpectedly refused: %+v %v", rel, err)
	}
}
