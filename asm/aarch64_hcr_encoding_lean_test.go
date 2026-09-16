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
	hcrWriteEncodingName = "MSR_SR_systemmove"
	hcrEl2X0Text         = "msr hcr_el2, x0"
	hcrEl2X0Word         = uint32(0xd51c1100)
)

var aarch64HCRLeanWordBlock = regexp.MustCompile(
	`(?s)-- OAK-A64-HCR-EL2-WORD-BEGIN[^\n]*\n(.*?)-- OAK-A64-HCR-EL2-WORD-END`,
)

func TestAArch64HCREL2X0LeanEncodingMatchesTables(t *testing.T) {
	var encoding *isaEncoding
	encodingMatches := 0
	for index := range isaEncodings {
		if isaEncodings[index].Name == hcrWriteEncodingName {
			encodingMatches++
			encoding = &isaEncodings[index]
		}
	}
	if encodingMatches != 1 {
		t.Fatalf("generated AArch64 table has %d %s encodings, want 1",
			encodingMatches, hcrWriteEncodingName)
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
			hcrWriteEncodingName, encoding)
	}

	hcr, ok := systemRegisterEncodings["hcr_el2"]
	if !ok {
		t.Fatal("generated SysReg table lacks hcr_el2")
	}
	wantHCR := sysRegEncoding{Op0: 3, Op1: 4, CRn: 1, CRm: 1, Op2: 0, Read: true, Write: true}
	if hcr != wantHCR {
		t.Fatalf("hcr_el2 tuple = %#v, want %#v", hcr, wantHCR)
	}

	path := filepath.Join("..", "spec", "lean", "Oak", "AArch64Encoding.lean")
	contents, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	wordMatch := aarch64HCRLeanWordBlock.FindStringSubmatch(string(contents))
	if wordMatch == nil {
		t.Fatalf("%s lacks its exact HCR_EL2 word block", path)
	}
	wantWordBlock := fmt.Sprintf(
		"def msrHcrEl2X0 : BitVec 32 := "+
			"encodeSystemMsr 0b1#1 0b100#3 0b0001#4 0b0001#4 0b000#3 0b00000#5 "+
			"theorem msr_hcr_el2_x0_word : msrHcrEl2X0 = 0x%08x#32 := by native_decide",
		hcrEl2X0Word,
	)
	if got := strings.Join(strings.Fields(wordMatch[1]), " "); got != wantWordBlock {
		t.Fatalf("%s exact HCR_EL2 word block drifted:\n--- have\n%s\n--- want\n%s",
			path, got, wantWordBlock)
	}
}

func TestAArch64HCREL2X0ExactWord(t *testing.T) {
	got, err := encodeText(t, hcrEl2X0Text)
	if err != nil {
		t.Fatalf("encode %q: %v", hcrEl2X0Text, err)
	}
	if got != hcrEl2X0Word {
		t.Fatalf("encode %q = %08x, want %08x", hcrEl2X0Text, got, hcrEl2X0Word)
	}
}
