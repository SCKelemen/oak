package asm

import (
	"fmt"
	"os"
	"path/filepath"
	"reflect"
	"regexp"
	"strings"
	"testing"
)

const (
	daifSetEncodingName = "MSR_SI_pstate"
	daifSetIRQText      = "msr daifset, #2"
	daifSetIRQWord      = uint32(0xd50342df)
)

var aarch64PSTATELeanEncodingBlock = regexp.MustCompile(
	`(?s)-- OAK-A64-PSTATE-ENC-BEGIN[^\n]*\n(.*?)-- OAK-A64-PSTATE-ENC-END`,
)

var aarch64DAIFSetLeanWordBlock = regexp.MustCompile(
	`(?s)-- OAK-A64-DAIFSET-WORD-BEGIN[^\n]*\n(.*?)-- OAK-A64-DAIFSET-WORD-END`,
)

func TestAArch64DAIFSetIRQLeanEncodingMatchesTable(t *testing.T) {
	var encoding *isaEncoding
	encodingMatches := 0
	for index := range isaEncodings {
		if isaEncodings[index].Name == daifSetEncodingName {
			encodingMatches++
			encoding = &isaEncodings[index]
		}
	}
	if encodingMatches != 1 {
		t.Fatalf("generated AArch64 table has %d %s encodings, want 1",
			encodingMatches, daifSetEncodingName)
	}
	if encoding.Mnemonic != "msr" || encoding.Value != 0xd500401f || encoding.Mask != 0xfff8f01f {
		t.Fatalf("%s metadata = mnemonic %q value %08x mask %08x",
			daifSetEncodingName, encoding.Mnemonic, encoding.Value, encoding.Mask)
	}
	wantFields := []isaField{
		{Name: "op1", Hi: 18, Width: 3},
		{Name: "CRm", Hi: 11, Width: 4},
		{Name: "op2", Hi: 7, Width: 3},
		{Name: "Rt", Hi: 4, Width: 5},
	}
	if !reflect.DeepEqual(encoding.Fields, wantFields) {
		t.Fatalf("%s fields = %#v, want %#v", daifSetEncodingName, encoding.Fields, wantFields)
	}

	formMatches := 0
	for _, form := range encoding.Forms {
		if len(form.Operands) != 2 {
			continue
		}
		field, immediate := form.Operands[0], form.Operands[1]
		if field.Sym != "<pstatefield>" || field.Kind != "table" ||
			!reflect.DeepEqual(field.Fields, []string{"CRm", "op1", "op2"}) ||
			immediate.Sym != "#<imm>" || immediate.Kind != "imm" ||
			!reflect.DeepEqual(immediate.Fields, []string{"CRm"}) ||
			!immediate.HasRange || immediate.Min != 0 || immediate.Max != 15 {
			continue
		}
		for _, row := range field.Table {
			if row.Text == "DAIFSET" {
				formMatches++
				if want := []string{"xxxx", "011", "110"}; !reflect.DeepEqual(row.Bits, want) {
					t.Fatalf("DAIFSET fields = %v, want %v", row.Bits, want)
				}
			}
		}
	}
	if formMatches != 1 {
		t.Fatalf("generated PSTATE table has %d DAIFSET immediate rows, want 1", formMatches)
	}

	path := filepath.Join("..", "spec", "lean", "Oak", "AArch64Encoding.lean")
	contents, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	encodingMatch := aarch64PSTATELeanEncodingBlock.FindStringSubmatch(string(contents))
	if encodingMatch == nil {
		t.Fatalf("%s lacks its generated PSTATE encoding block", path)
	}
	var leanFields []string
	for _, field := range wantFields {
		leanFields = append(leanFields, fmt.Sprintf("⟨%q, %d, %d⟩", field.Name, field.Hi, field.Width))
	}
	wantEncoding := fmt.Sprintf("def msrPstate : Encoding := ⟨%q, %q, 0x%08x#32, 0x%08x#32, [%s]⟩",
		encoding.Name, encoding.Mnemonic, encoding.Value, encoding.Mask, strings.Join(leanFields, ", "))
	if got := strings.TrimSpace(encodingMatch[1]); got != wantEncoding {
		t.Fatalf("%s PSTATE encoding drifted from asm/encodings_gen.go:\n--- have\n%s\n--- want\n%s",
			path, got, wantEncoding)
	}

	wordMatch := aarch64DAIFSetLeanWordBlock.FindStringSubmatch(string(contents))
	if wordMatch == nil {
		t.Fatalf("%s lacks its exact DAIFSet word block", path)
	}
	wantWordBlock := "def msrDaifSetIrq : BitVec 32 := " +
		"encodePstateImmediate 0b011#3 0b0010#4 0b110#3 " +
		"theorem msr_daifset_irq_word : msrDaifSetIrq = 0xd50342df#32 := by native_decide"
	if got := strings.Join(strings.Fields(wordMatch[1]), " "); got != wantWordBlock {
		t.Fatalf("%s exact DAIFSet word block drifted:\n--- have\n%s\n--- want\n%s",
			path, got, wantWordBlock)
	}
}

func TestAArch64DAIFSetIRQExactWord(t *testing.T) {
	got, err := encodeText(t, daifSetIRQText)
	if err != nil {
		t.Fatalf("encode %q: %v", daifSetIRQText, err)
	}
	if got != daifSetIRQWord {
		t.Fatalf("encode %q = %08x, want %08x", daifSetIRQText, got, daifSetIRQWord)
	}
}
