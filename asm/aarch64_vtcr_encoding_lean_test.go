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
	vtcrWriteEncodingName = "MSR_SR_systemmove"
	vtcrEl2X2Text         = "msr vtcr_el2, x2"
	vtcrEl2X2Word         = uint32(0xd51c2142)
)

var aarch64VTCRLeanWordBlock = regexp.MustCompile(
	`(?s)-- OAK-A64-VTCR-EL2-WORD-BEGIN[^\n]*\n(.*?)-- OAK-A64-VTCR-EL2-WORD-END`,
)

func TestAArch64VTCREL2X2LeanEncodingMatchesTables(t *testing.T) {
	var encoding *isaEncoding
	encodingMatches := 0
	for index := range isaEncodings {
		if isaEncodings[index].Name == vtcrWriteEncodingName {
			encodingMatches++
			encoding = &isaEncodings[index]
		}
	}
	if encodingMatches != 1 {
		t.Fatalf("generated AArch64 table has %d %s encodings, want 1",
			encodingMatches, vtcrWriteEncodingName)
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
			vtcrWriteEncodingName, encoding)
	}

	vtcr, ok := systemRegisterEncodings["vtcr_el2"]
	if !ok {
		t.Fatal("generated SysReg table lacks vtcr_el2")
	}
	wantVTCR := sysRegEncoding{Op0: 3, Op1: 4, CRn: 2, CRm: 1, Op2: 2, Read: true, Write: true}
	if vtcr != wantVTCR {
		t.Fatalf("vtcr_el2 tuple = %#v, want %#v", vtcr, wantVTCR)
	}

	path := filepath.Join("..", "spec", "lean", "Oak", "AArch64Encoding.lean")
	contents, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	wordMatch := aarch64VTCRLeanWordBlock.FindStringSubmatch(string(contents))
	if wordMatch == nil {
		t.Fatalf("%s lacks its exact VTCR_EL2 word block", path)
	}
	wantWordBlock := fmt.Sprintf(
		"def msrVtcrEl2X2 : BitVec 32 := "+
			"encodeSystemMsr 0b1#1 0b100#3 0b0010#4 0b0001#4 0b010#3 0b00010#5 "+
			"theorem msr_vtcr_el2_x2_word : msrVtcrEl2X2 = 0x%08x#32 := by native_decide",
		vtcrEl2X2Word,
	)
	if got := strings.Join(strings.Fields(wordMatch[1]), " "); got != wantWordBlock {
		t.Fatalf("%s exact VTCR_EL2 word block drifted:\n--- have\n%s\n--- want\n%s",
			path, got, wantWordBlock)
	}
}

func TestAArch64VTCREL2X2ExactWord(t *testing.T) {
	got, err := encodeText(t, vtcrEl2X2Text)
	if err != nil {
		t.Fatalf("encode %q: %v", vtcrEl2X2Text, err)
	}
	if got != vtcrEl2X2Word {
		t.Fatalf("encode %q = %08x, want %08x", vtcrEl2X2Text, got, vtcrEl2X2Word)
	}
}
