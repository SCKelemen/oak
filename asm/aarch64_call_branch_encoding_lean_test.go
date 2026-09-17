package asm

import (
	"bytes"
	"encoding/binary"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
)

const aarch64BLEncodingName = "BL_only_branch_imm"

var aarch64BLFields = []isaField{
	{Name: "op", Hi: 31, Width: 1},
	{Name: "imm26", Hi: 25, Width: 26},
}

var aarch64BLEncodingBlock = regexp.MustCompile(
	`(?s)-- OAK-A64-BL-ENC-BEGIN[^\n]*\n(.*?)-- OAK-A64-BL-ENC-END`,
)

var aarch64BLWordBlock = regexp.MustCompile(
	`(?s)-- OAK-A64-BL-WORD-BEGIN[^\n]*\n(.*?)-- OAK-A64-BL-WORD-END`,
)

func aarch64BLEncoding(t *testing.T) isaEncoding {
	t.Helper()
	var matches []isaEncoding
	for _, encoding := range isaEncodings {
		if encoding.Name == aarch64BLEncodingName {
			matches = append(matches, encoding)
		}
	}
	if len(matches) != 1 {
		t.Fatalf("generated AArch64 table has %d %s rows, want one",
			len(matches), aarch64BLEncodingName)
	}
	return matches[0]
}

func aarch64BLBlockLines(block string) []string {
	var lines []string
	for _, line := range strings.Split(block, "\n") {
		line = strings.TrimSpace(line)
		if strings.HasPrefix(line, "def ") || strings.HasPrefix(line, "theorem ") {
			lines = append(lines, line)
		}
	}
	return lines
}

func TestAArch64CallBranchLeanEncodingMatchesTable(t *testing.T) {
	encoding := aarch64BLEncoding(t)
	if encoding.Mnemonic != "bl" || encoding.Mask != 0xfc000000 || encoding.Value != 0x94000000 {
		t.Fatalf("generated BL row is %s mask=%#08x value=%#08x",
			encoding.Mnemonic, encoding.Mask, encoding.Value)
	}
	if len(encoding.Fields) != len(aarch64BLFields) {
		t.Fatalf("generated BL fields = %+v, want %+v", encoding.Fields, aarch64BLFields)
	}
	for index, want := range aarch64BLFields {
		if encoding.Fields[index] != want {
			t.Fatalf("generated BL field %d = %+v, want %+v", index, encoding.Fields[index], want)
		}
	}
	if len(encoding.Forms) != 1 || len(encoding.Forms[0].Operands) != 1 ||
		len(encoding.Forms[0].Defaults) != 0 {
		t.Fatalf("generated BL forms = %+v, want one label operand", encoding.Forms)
	}
	label := encoding.Forms[0].Operands[0]
	if label.Sym != "<label>" || label.Kind != "label" ||
		len(label.Fields) != 1 || label.Fields[0] != "imm26" ||
		!label.HasRange || label.Min != -(1<<27) || label.Max != (1<<27)-1 ||
		label.Scale != 4 {
		t.Fatalf("generated BL label operand = %+v", label)
	}

	path := filepath.Join("..", "spec", "lean", "Oak", "AArch64CallBranchEncoding.lean")
	contents, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	encodingMatch := aarch64BLEncodingBlock.FindStringSubmatch(string(contents))
	if encodingMatch == nil {
		t.Fatalf("%s lacks its generated BL-encoding block", path)
	}
	wantEncoding := []string{
		`def bl : Encoding := ⟨"BL_only_branch_imm", "bl", 0x94000000#32, 0xfc000000#32, [⟨"op", 31, 1⟩, ⟨"imm26", 25, 26⟩]⟩`,
	}
	gotEncoding := aarch64BLBlockLines(encodingMatch[1])
	if strings.Join(gotEncoding, "\n") != strings.Join(wantEncoding, "\n") {
		t.Fatalf("%s drifted from asm/encodings_gen.go:\n--- have\n%s\n--- want\n%s",
			path, strings.Join(gotEncoding, "\n"), strings.Join(wantEncoding, "\n"))
	}
	wordMatch := aarch64BLWordBlock.FindStringSubmatch(string(contents))
	if wordMatch == nil {
		t.Fatalf("%s lacks its exact BL-word block", path)
	}
	wantWords := []string{
		"def encodeBLImm26 (imm26 : BitVec 26) : BitVec 32 :=",
		"def blPlus12 : BitVec 32 := encodeBLImm26 3#26",
		"theorem bl_plus_12_word : blPlus12 = 0x94000003#32 := by native_decide",
	}
	gotWords := aarch64BLBlockLines(wordMatch[1])
	if strings.Join(gotWords, "\n") != strings.Join(wantWords, "\n") {
		t.Fatalf("%s exact BL word/formula drifted:\n--- have\n%s\n--- want\n%s",
			path, strings.Join(gotWords, "\n"), strings.Join(wantWords, "\n"))
	}
}

func encodeLocalBL(pc, target int64) (uint32, *Relocation, error) {
	return EncodeInstruction(Instruction{
		Mnemonic: "bl",
		Operands: []Operand{Symbol{Name: "target"}},
	}, pc, map[string]int64{"target": target})
}

func TestAArch64CallBranchLocalEncodingMatchesLean(t *testing.T) {
	const (
		maxInt64 = int64(^uint64(0) >> 1)
		minInt64 = -maxInt64 - 1
	)
	tests := []struct {
		name       string
		pc, target int64
		word       uint32
		accept     bool
	}{
		{name: "zero", pc: 0, target: 0, word: 0x94000000, accept: true},
		{name: "plus twelve", pc: 0x10000, target: 0x1000c, word: 0x94000003, accept: true},
		{name: "minus four", pc: 4, target: 0, word: 0x97ffffff, accept: true},
		{name: "negative endpoint", pc: 1 << 27, target: 0, word: 0x96000000, accept: true},
		{name: "positive endpoint", pc: 0, target: (1 << 27) - 4, word: 0x95ffffff, accept: true},
		{name: "below negative endpoint", pc: (1 << 27) + 4, target: 0},
		{name: "above positive endpoint", pc: 0, target: 1 << 27},
		{name: "misaligned target", pc: 0, target: 2},
		{name: "misaligned place", pc: 2, target: 4},
		{name: "jointly misaligned", pc: 1, target: 5},
		{name: "positive subtraction overflow", pc: minInt64 + 4, target: maxInt64 - 3},
		{name: "negative subtraction overflow", pc: maxInt64 - 3, target: minInt64 + 4},
	}

	var leanExamples []string
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			word, relocation, err := encodeLocalBL(test.pc, test.target)
			if test.accept {
				if err != nil {
					t.Fatalf("encode local BL: %v", err)
				}
				if relocation != nil {
					t.Fatalf("local BL emitted relocation %+v", relocation)
				}
				if word != test.word {
					t.Fatalf("local BL %#x -> %#x = %#08x, want %#08x",
						test.pc, test.target, word, test.word)
				}
			} else {
				if err == nil {
					t.Fatalf("local BL %#x -> %#x encoded %#08x, want refusal",
						test.pc, test.target, word)
				}
				if word != 0 || relocation != nil {
					t.Fatalf("refused local BL returned word %#08x relocation %+v", word, relocation)
				}
			}

			result := "none"
			if test.accept {
				result = fmt.Sprintf("some 0x%08x#32", word)
			}
			leanExamples = append(leanExamples, fmt.Sprintf(
				"example : relocateBranch26 .call bl.value (%d : Int) (%d : Int) = %s := by decide",
				test.pc, test.target, result))
		})
	}

	lake, err := exec.LookPath("lake")
	if err != nil {
		t.Skip("lake not on PATH; the formal workflow runs this kernel oracle")
	}
	leanPath := filepath.Join(t.TempDir(), "AArch64CallBranchProductionPins.lean")
	leanSource := "import Oak.AArch64CallBranchEncoding\n\n" +
		"namespace Oak.AArch64CallBranchEncoding\n\n" +
		"open Oak.ObjectRelocation\n\n" +
		strings.Join(leanExamples, "\n") +
		"\n\nend Oak.AArch64CallBranchEncoding\n"
	if err := os.WriteFile(leanPath, []byte(leanSource), 0o600); err != nil {
		t.Fatal(err)
	}
	buildLeanImports(t, lake, leanPath)
	command := exec.Command(lake, "env", "lean", leanPath)
	command.Dir = filepath.Join("..", "spec", "lean")
	if output, err := command.CombinedOutput(); err != nil {
		t.Fatalf("kernel-checking local BL pins: %v\n%s\n--- source ---\n%s",
			err, output, leanSource)
	}
}

func TestAArch64CallBranchFunctionExactBytes(t *testing.T) {
	unit, diagnostics := ParseUnit("call_word.arm64.oakasm", `call_word: () -> () = {
  clobber x30
  bl done
done:
  ret
}
`)
	if len(diagnostics) != 0 || unit == nil || len(unit.Functions) != 1 {
		t.Fatalf("parse direct-BL function: %v", diagnostics)
	}
	code, relocations, err := EncodeFunction(unit.Functions[0])
	if err != nil {
		t.Fatal(err)
	}
	if len(relocations) != 0 {
		t.Fatalf("local direct BL emitted relocations: %+v", relocations)
	}
	want := []byte{0x01, 0x00, 0x00, 0x94, 0xc0, 0x03, 0x5f, 0xd6}
	if !bytes.Equal(code, want) {
		t.Fatalf("direct-BL function bytes = %x, want %x", code, want)
	}
}

func TestAArch64CallBranchRelocationBoundaryRefusalDoesNotMutate(t *testing.T) {
	const maxUint64 = ^uint64(0)
	tests := []struct {
		name          string
		place, target uint64
	}{
		{name: "huge negative delta", place: maxUint64 - 3, target: 0},
		{name: "huge positive delta", place: 0, target: maxUint64 - 3},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			text := make([]byte, 4)
			binary.LittleEndian.PutUint32(text, 0x94000003)
			before := append([]byte(nil), text...)
			layout := &textLayout{
				text: text,
				relocs: []placedReloc{{
					offset: 0,
					kind:   "call26",
					symbol: "target",
				}},
			}
			err := resolveRelocations(layout, test.place,
				map[string]uint64{"target": test.target})
			if err == nil {
				t.Fatal("resolveRelocations accepted an out-of-range direct BL")
			}
			if !bytes.Equal(layout.text, before) {
				t.Fatalf("resolveRelocations mutated BL text on refusal: %x -> %x",
					before, layout.text)
			}
		})
	}
}
