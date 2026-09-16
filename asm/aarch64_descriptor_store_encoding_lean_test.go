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
	descriptorStoreEncodingName = "STR_64_ldst_pos"
	descriptorBreakText         = "str xzr, [x0]"
	descriptorBreakWord         = uint32(0xf900001f)
	descriptorMakeText          = "str x2, [x0]"
	descriptorMakeWord          = uint32(0xf9000002)
)

var aarch64DescriptorStoreLeanEncodingBlock = regexp.MustCompile(
	`(?s)-- OAK-A64-STR64-ENC-BEGIN[^\n]*\n(.*?)-- OAK-A64-STR64-ENC-END`,
)

var aarch64DescriptorStoreLeanWordBlock = regexp.MustCompile(
	`(?s)-- OAK-A64-DESCRIPTOR-STORE-WORD-BEGIN[^\n]*\n(.*?)-- OAK-A64-DESCRIPTOR-STORE-WORD-END`,
)

func TestAArch64DescriptorStoreLeanEncodingMatchesTable(t *testing.T) {
	var encoding *isaEncoding
	for index := range isaEncodings {
		if isaEncodings[index].Name == descriptorStoreEncodingName {
			encoding = &isaEncodings[index]
			break
		}
	}
	if encoding == nil {
		t.Fatalf("generated AArch64 table lacks %s", descriptorStoreEncodingName)
	}
	if encoding.Mnemonic != "str" || encoding.Value != 0xf9000000 || encoding.Mask != 0xffc00000 {
		t.Fatalf("%s metadata = mnemonic %q value %08x mask %08x",
			descriptorStoreEncodingName, encoding.Mnemonic, encoding.Value, encoding.Mask)
	}
	wantFields := []isaField{
		{Name: "size", Hi: 31, Width: 2},
		{Name: "VR", Hi: 26, Width: 1},
		{Name: "opc", Hi: 23, Width: 2},
		{Name: "imm12", Hi: 21, Width: 12},
		{Name: "Rn", Hi: 9, Width: 5},
		{Name: "Rt", Hi: 4, Width: 5},
	}
	if !reflect.DeepEqual(encoding.Fields, wantFields) {
		t.Fatalf("%s fields = %#v, want %#v", descriptorStoreEncodingName,
			encoding.Fields, wantFields)
	}
	wantZeroOffsetForm := isaForm{
		Operands: []isaOperand{
			{Sym: "<Xt>", Kind: "gp", Fields: []string{"Rt"}, Width: 64, ZR: true},
			{Sym: "[<Xn|SP>]", Kind: "mem", Mode: "off", Sub: []isaOperand{
				{Sym: "<Xn|SP>", Kind: "gp", Fields: []string{"Rn"}, Width: 64, SP: true},
			}},
		},
		Defaults: []isaDefault{{Field: "imm12", Value: 0}},
	}
	zeroOffsetForms := 0
	for _, form := range encoding.Forms {
		if reflect.DeepEqual(form, wantZeroOffsetForm) {
			zeroOffsetForms++
		}
	}
	if zeroOffsetForms != 1 {
		t.Fatalf("generated STR table has %d exact zero-offset 64-bit forms, want 1",
			zeroOffsetForms)
	}

	path := filepath.Join("..", "spec", "lean", "Oak", "AArch64Encoding.lean")
	contents, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	encodingMatch := aarch64DescriptorStoreLeanEncodingBlock.FindStringSubmatch(string(contents))
	if encodingMatch == nil {
		t.Fatalf("%s lacks its generated STR64 encoding block", path)
	}
	var leanFields []string
	for _, field := range wantFields {
		leanFields = append(leanFields, fmt.Sprintf("⟨%q, %d, %d⟩",
			field.Name, field.Hi, field.Width))
	}
	wantEncoding := fmt.Sprintf(
		"def str64UnsignedOffset : Encoding := ⟨%q, %q, 0x%08x#32, 0x%08x#32, [%s]⟩",
		encoding.Name, encoding.Mnemonic, encoding.Value, encoding.Mask,
		strings.Join(leanFields, ", "))
	if got := strings.TrimSpace(encodingMatch[1]); got != wantEncoding {
		t.Fatalf("%s STR64 encoding drifted from asm/encodings_gen.go:\n--- have\n%s\n--- want\n%s",
			path, got, wantEncoding)
	}

	wordMatch := aarch64DescriptorStoreLeanWordBlock.FindStringSubmatch(string(contents))
	if wordMatch == nil {
		t.Fatalf("%s lacks its exact descriptor-store word block", path)
	}
	wantWordBlock := "def strXzrX0 : BitVec 32 := " +
		"encodeStr64UnsignedOffset 0#12 0#5 0b11111#5 " +
		"def strX2X0 : BitVec 32 := encodeStr64UnsignedOffset 0#12 0#5 2#5 " +
		"theorem str_xzr_x0_word : strXzrX0 = 0xf900001f#32 := by native_decide " +
		"theorem str_x2_x0_word : strX2X0 = 0xf9000002#32 := by native_decide"
	if got := strings.Join(strings.Fields(wordMatch[1]), " "); got != wantWordBlock {
		t.Fatalf("%s exact descriptor-store word block drifted:\n--- have\n%s\n--- want\n%s",
			path, got, wantWordBlock)
	}
}

func TestAArch64DescriptorStoreExactWords(t *testing.T) {
	for _, test := range []struct {
		text string
		word uint32
	}{
		{descriptorBreakText, descriptorBreakWord},
		{descriptorMakeText, descriptorMakeWord},
	} {
		got, err := encodeText(t, test.text)
		if err != nil {
			t.Fatalf("encode %q: %v", test.text, err)
		}
		if got != test.word {
			t.Fatalf("encode %q = %08x, want %08x", test.text, got, test.word)
		}
	}
	nearbyMake, err := encodeText(t, "str x1, [x0]")
	if err != nil {
		t.Fatal(err)
	}
	if nearbyMake != 0xf9000001 || nearbyMake == descriptorMakeWord {
		t.Fatalf("nearby Rt encoding = %08x; make = %08x", nearbyMake, descriptorMakeWord)
	}
	nearbyBreak, err := encodeText(t, "str xzr, [x1]")
	if err != nil {
		t.Fatal(err)
	}
	if nearbyBreak != 0xf900003f || nearbyBreak == descriptorBreakWord {
		t.Fatalf("nearby Rn encoding = %08x; break = %08x", nearbyBreak, descriptorBreakWord)
	}
}
