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
	spsrEl2WriteEncodingName = "MSR_SR_systemmove"
	spsrEl2X7Text            = "msr spsr_el2, x7"
	spsrEl2X7Word            = uint32(0xd51c4007)
)

var aarch64SPSREL2LeanWordBlock = regexp.MustCompile(
	`(?s)-- OAK-A64-SPSR-EL2-WORD-BEGIN[^\n]*\n(.*?)-- OAK-A64-SPSR-EL2-WORD-END`,
)

func TestAArch64SPSREL2X7LeanEncodingMatchesTables(t *testing.T) {
	var encoding *isaEncoding
	encodingMatches := 0
	for index := range isaEncodings {
		if isaEncodings[index].Name == spsrEl2WriteEncodingName {
			encodingMatches++
			encoding = &isaEncodings[index]
		}
	}
	if encodingMatches != 1 {
		t.Fatalf("generated AArch64 table has %d %s encodings, want 1",
			encodingMatches, spsrEl2WriteEncodingName)
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
			spsrEl2WriteEncodingName, encoding)
	}

	spsrEl2, ok := systemRegisterEncodings["spsr_el2"]
	if !ok {
		t.Fatal("generated SysReg table lacks spsr_el2")
	}
	wantSPSREL2 := sysRegEncoding{Op0: 3, Op1: 4, CRn: 4, CRm: 0, Op2: 0, Read: true, Write: true}
	if spsrEl2 != wantSPSREL2 {
		t.Fatalf("spsr_el2 tuple = %#v, want %#v", spsrEl2, wantSPSREL2)
	}

	path := filepath.Join("..", "spec", "lean", "Oak", "AArch64Encoding.lean")
	contents, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	wordMatch := aarch64SPSREL2LeanWordBlock.FindStringSubmatch(string(contents))
	if wordMatch == nil {
		t.Fatalf("%s lacks its exact SPSR_EL2 word block", path)
	}
	wantWordBlock := fmt.Sprintf(
		"def msrSpsrEl2X7 : BitVec 32 := "+
			"encodeSystemMsr 0b1#1 0b100#3 0b0100#4 0b0000#4 0b000#3 0b00111#5 "+
			"theorem msr_spsr_el2_x7_word : msrSpsrEl2X7 = 0x%08x#32 := by native_decide",
		spsrEl2X7Word,
	)
	if got := strings.Join(strings.Fields(wordMatch[1]), " "); got != wantWordBlock {
		t.Fatalf("%s exact SPSR_EL2 word block drifted:\n--- have\n%s\n--- want\n%s",
			path, got, wantWordBlock)
	}
}

func TestAArch64SPSREL2X7ExactWord(t *testing.T) {
	got, err := encodeText(t, spsrEl2X7Text)
	if err != nil {
		t.Fatalf("encode %q: %v", spsrEl2X7Text, err)
	}
	if got != spsrEl2X7Word {
		t.Fatalf("encode %q = %08x, want %08x", spsrEl2X7Text, got, spsrEl2X7Word)
	}
}
