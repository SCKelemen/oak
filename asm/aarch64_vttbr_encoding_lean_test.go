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
	vttbrWriteEncodingName = "MSR_SR_systemmove"
	vttbrEl2X1Text         = "msr vttbr_el2, x1"
	vttbrEl2X1Word         = uint32(0xd51c2101)
)

var aarch64SysRegWriteLeanEncodingBlock = regexp.MustCompile(
	`(?s)-- OAK-A64-SYSREG-WRITE-ENC-BEGIN[^\n]*\n(.*?)-- OAK-A64-SYSREG-WRITE-ENC-END`,
)

var aarch64VTTBRLeanWordBlock = regexp.MustCompile(
	`(?s)-- OAK-A64-VTTBR-EL2-WORD-BEGIN[^\n]*\n(.*?)-- OAK-A64-VTTBR-EL2-WORD-END`,
)

func TestAArch64VTTBREL2X1LeanEncodingMatchesTables(t *testing.T) {
	var encoding *isaEncoding
	encodingMatches := 0
	for index := range isaEncodings {
		if isaEncodings[index].Name == vttbrWriteEncodingName {
			encodingMatches++
			encoding = &isaEncodings[index]
		}
	}
	if encodingMatches != 1 {
		t.Fatalf("generated AArch64 table has %d %s encodings, want 1",
			encodingMatches, vttbrWriteEncodingName)
	}
	if encoding.Mnemonic != "msr" || encoding.Value != 0xd5100000 ||
		encoding.Mask != 0xfff00000 {
		t.Fatalf("%s metadata = mnemonic %q value %08x mask %08x",
			vttbrWriteEncodingName, encoding.Mnemonic, encoding.Value, encoding.Mask)
	}
	wantFields := []isaField{
		{Name: "L", Hi: 21, Width: 1},
		{Name: "o0", Hi: 19, Width: 1},
		{Name: "op1", Hi: 18, Width: 3},
		{Name: "CRn", Hi: 15, Width: 4},
		{Name: "CRm", Hi: 11, Width: 4},
		{Name: "op2", Hi: 7, Width: 3},
		{Name: "Rt", Hi: 4, Width: 5},
	}
	if !reflect.DeepEqual(encoding.Fields, wantFields) {
		t.Fatalf("%s fields = %#v, want %#v", vttbrWriteEncodingName, encoding.Fields, wantFields)
	}
	wantOperands := []isaOperand{
		{Sym: "<systemreg>", Kind: "sysreg", Fields: []string{"o0", "op1", "CRn", "CRm", "op2"}},
		{Sym: "<Xt>", Kind: "gp", Fields: []string{"Rt"}, Width: 64, ZR: true},
	}
	if len(encoding.Forms) != 1 || !reflect.DeepEqual(encoding.Forms[0].Operands, wantOperands) {
		t.Fatalf("%s forms = %#v, want one exact general-MSR form",
			vttbrWriteEncodingName, encoding.Forms)
	}

	vttbr, ok := systemRegisterEncodings["vttbr_el2"]
	if !ok {
		t.Fatal("generated SysReg table lacks vttbr_el2")
	}
	wantVTTBR := sysRegEncoding{Op0: 3, Op1: 4, CRn: 2, CRm: 1, Op2: 0, Read: true, Write: true}
	if vttbr != wantVTTBR {
		t.Fatalf("vttbr_el2 tuple = %#v, want %#v", vttbr, wantVTTBR)
	}

	path := filepath.Join("..", "spec", "lean", "Oak", "AArch64Encoding.lean")
	contents, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	encodingMatch := aarch64SysRegWriteLeanEncodingBlock.FindStringSubmatch(string(contents))
	if encodingMatch == nil {
		t.Fatalf("%s lacks its generated system-register write encoding block", path)
	}
	var leanFields []string
	for _, field := range wantFields {
		leanFields = append(leanFields, fmt.Sprintf("⟨%q, %d, %d⟩", field.Name, field.Hi, field.Width))
	}
	wantEncoding := fmt.Sprintf("def msrSystem : Encoding := ⟨%q, %q, 0x%08x#32, 0x%08x#32, [%s]⟩",
		encoding.Name, encoding.Mnemonic, encoding.Value, encoding.Mask, strings.Join(leanFields, ", "))
	if got := strings.TrimSpace(encodingMatch[1]); got != wantEncoding {
		t.Fatalf("%s system-register encoding drifted:\n--- have\n%s\n--- want\n%s",
			path, got, wantEncoding)
	}

	wordMatch := aarch64VTTBRLeanWordBlock.FindStringSubmatch(string(contents))
	if wordMatch == nil {
		t.Fatalf("%s lacks its exact VTTBR_EL2 word block", path)
	}
	wantWordBlock := "def msrVttbrEl2X1 : BitVec 32 := " +
		"encodeSystemMsr 0b1#1 0b100#3 0b0010#4 0b0001#4 0b000#3 0b00001#5 " +
		"theorem msr_vttbr_el2_x1_word : msrVttbrEl2X1 = 0xd51c2101#32 := by native_decide"
	if got := strings.Join(strings.Fields(wordMatch[1]), " "); got != wantWordBlock {
		t.Fatalf("%s exact VTTBR_EL2 word block drifted:\n--- have\n%s\n--- want\n%s",
			path, got, wantWordBlock)
	}
}

func TestAArch64VTTBREL2X1ExactWord(t *testing.T) {
	got, err := encodeText(t, vttbrEl2X1Text)
	if err != nil {
		t.Fatalf("encode %q: %v", vttbrEl2X1Text, err)
	}
	if got != vttbrEl2X1Word {
		t.Fatalf("encode %q = %08x, want %08x", vttbrEl2X1Text, got, vttbrEl2X1Word)
	}
}
