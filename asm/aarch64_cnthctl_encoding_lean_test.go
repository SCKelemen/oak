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
	cnthctlWriteEncodingName = "MSR_SR_systemmove"
	cnthctlEl2X3Text         = "msr cnthctl_el2, x3"
	cnthctlEl2X3Word         = uint32(0xd51ce103)
)

var aarch64CNTHCTLLeanWordBlock = regexp.MustCompile(
	`(?s)-- OAK-A64-CNTHCTL-EL2-WORD-BEGIN[^\n]*\n(.*?)-- OAK-A64-CNTHCTL-EL2-WORD-END`,
)

func TestAArch64CNTHCTLEL2X3LeanEncodingMatchesTables(t *testing.T) {
	var encoding *isaEncoding
	encodingMatches := 0
	for index := range isaEncodings {
		if isaEncodings[index].Name == cnthctlWriteEncodingName {
			encodingMatches++
			encoding = &isaEncodings[index]
		}
	}
	if encodingMatches != 1 {
		t.Fatalf("generated AArch64 table has %d %s encodings, want 1",
			encodingMatches, cnthctlWriteEncodingName)
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
	if encoding.Mnemonic != "msr" || encoding.Value != 0xd5100000 ||
		encoding.Mask != 0xfff00000 || !reflect.DeepEqual(encoding.Fields, wantFields) {
		t.Fatalf("%s no longer has the exact general-MSR encoding: %#v",
			cnthctlWriteEncodingName, encoding)
	}

	cnthctl, ok := systemRegisterEncodings["cnthctl_el2"]
	if !ok {
		t.Fatal("generated SysReg table lacks cnthctl_el2")
	}
	wantCNTHCTL := sysRegEncoding{Op0: 3, Op1: 4, CRn: 14, CRm: 1, Op2: 0, Read: true, Write: true}
	if cnthctl != wantCNTHCTL {
		t.Fatalf("cnthctl_el2 tuple = %#v, want %#v", cnthctl, wantCNTHCTL)
	}

	path := filepath.Join("..", "spec", "lean", "Oak", "AArch64Encoding.lean")
	contents, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	wordMatch := aarch64CNTHCTLLeanWordBlock.FindStringSubmatch(string(contents))
	if wordMatch == nil {
		t.Fatalf("%s lacks its exact CNTHCTL_EL2 word block", path)
	}
	wantWordBlock := fmt.Sprintf(
		"def msrCnthctlEl2X3 : BitVec 32 := "+
			"encodeSystemMsr 0b1#1 0b100#3 0b1110#4 0b0001#4 0b000#3 0b00011#5 "+
			"theorem msr_cnthctl_el2_x3_word : msrCnthctlEl2X3 = 0x%08x#32 := by native_decide",
		cnthctlEl2X3Word,
	)
	if got := strings.Join(strings.Fields(wordMatch[1]), " "); got != wantWordBlock {
		t.Fatalf("%s exact CNTHCTL_EL2 word block drifted:\n--- have\n%s\n--- want\n%s",
			path, got, wantWordBlock)
	}
}

func TestAArch64CNTHCTLEL2X3ExactWord(t *testing.T) {
	got, err := encodeText(t, cnthctlEl2X3Text)
	if err != nil {
		t.Fatalf("encode %q: %v", cnthctlEl2X3Text, err)
	}
	if got != cnthctlEl2X3Word {
		t.Fatalf("encode %q = %08x, want %08x", cnthctlEl2X3Text, got, cnthctlEl2X3Word)
	}
}
