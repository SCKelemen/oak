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
	vmalls12e1isEncodingName = "TLBI_SYS_CR_systeminstrs"
	vmalls12e1isText         = "tlbi vmalls12e1is"
	vmalls12e1isWord         = uint32(0xd50c83df)
	vmalls12e1Text           = "tlbi vmalls12e1"
	vmalls12e1Word           = uint32(0xd50c87df)
)

var aarch64TLBILeanEncodingBlock = regexp.MustCompile(
	`(?s)-- OAK-A64-TLBI-ENC-BEGIN[^\n]*\n(.*?)-- OAK-A64-TLBI-ENC-END`,
)

var aarch64TLBILeanWordBlock = regexp.MustCompile(
	`(?s)-- OAK-A64-TLBI-WORD-BEGIN[^\n]*\n(.*?)-- OAK-A64-TLBI-WORD-END`,
)

func TestAArch64VMALLS12E1ISLeanEncodingMatchesTable(t *testing.T) {
	var encoding *isaEncoding
	for index := range isaEncodings {
		if isaEncodings[index].Name == vmalls12e1isEncodingName {
			encoding = &isaEncodings[index]
			break
		}
	}
	if encoding == nil {
		t.Fatalf("generated AArch64 table lacks %s", vmalls12e1isEncodingName)
	}
	if encoding.Mnemonic != "tlbi" || encoding.Value != 0xd5088000 || encoding.Mask != 0xfff8e000 {
		t.Fatalf("%s metadata = mnemonic %q value %08x mask %08x",
			vmalls12e1isEncodingName, encoding.Mnemonic, encoding.Value, encoding.Mask)
	}
	wantFields := []isaField{
		{Name: "L", Hi: 21, Width: 1},
		{Name: "op1", Hi: 18, Width: 3},
		{Name: "CRn", Hi: 15, Width: 4},
		{Name: "CRm", Hi: 11, Width: 4},
		{Name: "op2", Hi: 7, Width: 3},
		{Name: "Rt", Hi: 4, Width: 5},
	}
	if !reflect.DeepEqual(encoding.Fields, wantFields) {
		t.Fatalf("%s fields = %#v, want %#v", vmalls12e1isEncodingName, encoding.Fields, wantFields)
	}

	wantBits := []string{"100", "1000", "0011", "110"}
	nullaryMatches := 0
	for _, form := range encoding.Forms {
		if len(form.Operands) != 1 {
			continue
		}
		operand := form.Operands[0]
		if operand.Sym != "<tlbi_op>" || operand.Kind != "table" ||
			!reflect.DeepEqual(operand.Fields, []string{"op1", "CRn", "CRm", "op2"}) {
			continue
		}
		for _, row := range operand.Table {
			if row.Text != "VMALLS12E1IS" {
				continue
			}
			nullaryMatches++
			if !reflect.DeepEqual(row.Bits, wantBits) {
				t.Fatalf("VMALLS12E1IS fields = %v, want %v", row.Bits, wantBits)
			}
			wantDefaults := []isaDefault{{Field: "Rt", Value: 31}}
			if !reflect.DeepEqual(form.Defaults, wantDefaults) {
				t.Fatalf("VMALLS12E1IS nullary defaults = %#v, want %#v",
					form.Defaults, wantDefaults)
			}
		}
	}
	if nullaryMatches != 1 {
		t.Fatalf("generated TLBI table has %d nullary VMALLS12E1IS rows, want 1",
			nullaryMatches)
	}

	path := filepath.Join("..", "spec", "lean", "Oak", "AArch64Encoding.lean")
	contents, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	encodingMatch := aarch64TLBILeanEncodingBlock.FindStringSubmatch(string(contents))
	if encodingMatch == nil {
		t.Fatalf("%s lacks its generated TLBI encoding block", path)
	}
	var leanFields []string
	for _, field := range wantFields {
		leanFields = append(leanFields, fmt.Sprintf("⟨%q, %d, %d⟩", field.Name, field.Hi, field.Width))
	}
	wantEncoding := fmt.Sprintf("def tlbi : Encoding := ⟨%q, %q, 0x%08x#32, 0x%08x#32, [%s]⟩",
		encoding.Name, encoding.Mnemonic, encoding.Value, encoding.Mask, strings.Join(leanFields, ", "))
	if got := strings.TrimSpace(encodingMatch[1]); got != wantEncoding {
		t.Fatalf("%s TLBI encoding drifted from asm/encodings_gen.go:\n--- have\n%s\n--- want\n%s",
			path, got, wantEncoding)
	}

	wordMatch := aarch64TLBILeanWordBlock.FindStringSubmatch(string(contents))
	if wordMatch == nil {
		t.Fatalf("%s lacks its exact TLBI word block", path)
	}
	wantWordBlock := "def tlbiVmalls12e1is : BitVec 32 := " +
		"encodeTlbiSys 0b100#3 0b1000#4 0b0011#4 0b110#3 0b11111#5 " +
		"theorem tlbi_vmalls12e1is_word : tlbiVmalls12e1is = 0xd50c83df#32 := by native_decide"
	if got := strings.Join(strings.Fields(wordMatch[1]), " "); got != wantWordBlock {
		t.Fatalf("%s exact TLBI word block drifted:\n--- have\n%s\n--- want\n%s",
			path, got, wantWordBlock)
	}
}

func TestAArch64VMALLS12E1ISExactWord(t *testing.T) {
	got, err := encodeText(t, vmalls12e1isText)
	if err != nil {
		t.Fatalf("encode %q: %v", vmalls12e1isText, err)
	}
	if got != vmalls12e1isWord {
		t.Fatalf("encode %q = %08x, want %08x", vmalls12e1isText, got, vmalls12e1isWord)
	}
}

func TestAArch64PlainVMALLS12E1DoesNotAliasInnerShareableWord(t *testing.T) {
	got, err := encodeText(t, vmalls12e1Text)
	if err != nil {
		t.Fatalf("encode %q: %v", vmalls12e1Text, err)
	}
	if got != vmalls12e1Word {
		t.Fatalf("encode %q = %08x, want %08x", vmalls12e1Text, got, vmalls12e1Word)
	}
	if got == vmalls12e1isWord {
		t.Fatalf("plain and Inner Shareable VMALLS12E1 words alias at %08x", got)
	}
}
