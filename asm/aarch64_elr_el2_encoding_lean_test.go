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
	elrEl2WriteEncodingName = "MSR_SR_systemmove"
	elrEl2X6Text            = "msr elr_el2, x6"
	elrEl2X6Word            = uint32(0xd51c4026)
)

var aarch64ELREL2LeanWordBlock = regexp.MustCompile(
	`(?s)-- OAK-A64-ELR-EL2-WORD-BEGIN[^\n]*\n(.*?)-- OAK-A64-ELR-EL2-WORD-END`,
)

func TestAArch64ELREL2X6LeanEncodingMatchesTables(t *testing.T) {
	var encoding *isaEncoding
	encodingMatches := 0
	for index := range isaEncodings {
		if isaEncodings[index].Name == elrEl2WriteEncodingName {
			encodingMatches++
			encoding = &isaEncodings[index]
		}
	}
	if encodingMatches != 1 {
		t.Fatalf("generated AArch64 table has %d %s encodings, want 1",
			encodingMatches, elrEl2WriteEncodingName)
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
			elrEl2WriteEncodingName, encoding)
	}

	elrEl2, ok := systemRegisterEncodings["elr_el2"]
	if !ok {
		t.Fatal("generated SysReg table lacks elr_el2")
	}
	wantELREL2 := sysRegEncoding{Op0: 3, Op1: 4, CRn: 4, CRm: 0, Op2: 1, Read: true, Write: true}
	if elrEl2 != wantELREL2 {
		t.Fatalf("elr_el2 tuple = %#v, want %#v", elrEl2, wantELREL2)
	}

	path := filepath.Join("..", "spec", "lean", "Oak", "AArch64Encoding.lean")
	contents, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	wordMatch := aarch64ELREL2LeanWordBlock.FindStringSubmatch(string(contents))
	if wordMatch == nil {
		t.Fatalf("%s lacks its exact ELR_EL2 word block", path)
	}
	wantWordBlock := fmt.Sprintf(
		"def msrElrEl2X6 : BitVec 32 := "+
			"encodeSystemMsr 0b1#1 0b100#3 0b0100#4 0b0000#4 0b001#3 0b00110#5 "+
			"theorem msr_elr_el2_x6_word : msrElrEl2X6 = 0x%08x#32 := by native_decide",
		elrEl2X6Word,
	)
	if got := strings.Join(strings.Fields(wordMatch[1]), " "); got != wantWordBlock {
		t.Fatalf("%s exact ELR_EL2 word block drifted:\n--- have\n%s\n--- want\n%s",
			path, got, wantWordBlock)
	}
}

func TestAArch64ELREL2X6ExactWord(t *testing.T) {
	got, err := encodeText(t, elrEl2X6Text)
	if err != nil {
		t.Fatalf("encode %q: %v", elrEl2X6Text, err)
	}
	if got != elrEl2X6Word {
		t.Fatalf("encode %q = %08x, want %08x", elrEl2X6Text, got, elrEl2X6Word)
	}
}
