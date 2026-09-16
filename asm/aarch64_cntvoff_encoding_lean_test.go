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
	cntvoffWriteEncodingName = "MSR_SR_systemmove"
	cntvoffEl2X4Text         = "msr cntvoff_el2, x4"
	cntvoffEl2X4Word         = uint32(0xd51ce064)
)

var aarch64CNTVOFFLeanWordBlock = regexp.MustCompile(
	`(?s)-- OAK-A64-CNTVOFF-EL2-WORD-BEGIN[^\n]*\n(.*?)-- OAK-A64-CNTVOFF-EL2-WORD-END`,
)

func TestAArch64CNTVOFFEL2X4LeanEncodingMatchesTables(t *testing.T) {
	var encoding *isaEncoding
	encodingMatches := 0
	for index := range isaEncodings {
		if isaEncodings[index].Name == cntvoffWriteEncodingName {
			encodingMatches++
			encoding = &isaEncodings[index]
		}
	}
	if encodingMatches != 1 {
		t.Fatalf("generated AArch64 table has %d %s encodings, want 1",
			encodingMatches, cntvoffWriteEncodingName)
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
			cntvoffWriteEncodingName, encoding)
	}

	cntvoff, ok := systemRegisterEncodings["cntvoff_el2"]
	if !ok {
		t.Fatal("generated SysReg table lacks cntvoff_el2")
	}
	wantCNTVOFF := sysRegEncoding{Op0: 3, Op1: 4, CRn: 14, CRm: 0, Op2: 3, Read: true, Write: true}
	if cntvoff != wantCNTVOFF {
		t.Fatalf("cntvoff_el2 tuple = %#v, want %#v", cntvoff, wantCNTVOFF)
	}

	path := filepath.Join("..", "spec", "lean", "Oak", "AArch64Encoding.lean")
	contents, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	wordMatch := aarch64CNTVOFFLeanWordBlock.FindStringSubmatch(string(contents))
	if wordMatch == nil {
		t.Fatalf("%s lacks its exact CNTVOFF_EL2 word block", path)
	}
	wantWordBlock := fmt.Sprintf(
		"def msrCntvoffEl2X4 : BitVec 32 := "+
			"encodeSystemMsr 0b1#1 0b100#3 0b1110#4 0b0000#4 0b011#3 0b00100#5 "+
			"theorem msr_cntvoff_el2_x4_word : msrCntvoffEl2X4 = 0x%08x#32 := by native_decide",
		cntvoffEl2X4Word,
	)
	if got := strings.Join(strings.Fields(wordMatch[1]), " "); got != wantWordBlock {
		t.Fatalf("%s exact CNTVOFF_EL2 word block drifted:\n--- have\n%s\n--- want\n%s",
			path, got, wantWordBlock)
	}
}

func TestAArch64CNTVOFFEL2X4ExactWord(t *testing.T) {
	got, err := encodeText(t, cntvoffEl2X4Text)
	if err != nil {
		t.Fatalf("encode %q: %v", cntvoffEl2X4Text, err)
	}
	if got != cntvoffEl2X4Word {
		t.Fatalf("encode %q = %08x, want %08x", cntvoffEl2X4Text, got, cntvoffEl2X4Word)
	}
}
