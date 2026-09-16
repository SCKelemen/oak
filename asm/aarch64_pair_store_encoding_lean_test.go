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
	aarch64STP64EncodingName = "STP_64_ldstpair_off"
	stpZeroPairText          = "stp xzr, xzr, [x0]"
	stpZeroPairWord          = uint32(0xa9007c1f)
	stpZeroPairPlus16Text    = "stp xzr, xzr, [x0, #16]"
	stpZeroPairPlus16Word    = uint32(0xa9017c1f)
)

var aarch64STP64LeanEncodingBlock = regexp.MustCompile(
	`(?s)-- OAK-A64-STP64-ENC-BEGIN[^\n]*\n(.*?)-- OAK-A64-STP64-ENC-END`,
)

var aarch64STP64LeanWordBlock = regexp.MustCompile(
	`(?s)-- OAK-A64-ZERO-PAIR-STORE-WORD-BEGIN[^\n]*\n(.*?)-- OAK-A64-ZERO-PAIR-STORE-WORD-END`,
)

func aarch64STP64GeneratedEncoding(t *testing.T) isaEncoding {
	t.Helper()
	var matches []isaEncoding
	for _, encoding := range isaEncodings {
		if encoding.Name == aarch64STP64EncodingName {
			matches = append(matches, encoding)
		}
	}
	if len(matches) != 1 {
		t.Fatalf("generated AArch64 table has %d %s rows, want one",
			len(matches), aarch64STP64EncodingName)
	}
	return matches[0]
}

func expectedAArch64STP64Encoding() isaEncoding {
	register := func(sym, field string) isaOperand {
		return isaOperand{Sym: sym, Kind: "gp", Fields: []string{field}, Width: 64, ZR: true}
	}
	base := isaOperand{Sym: "<Xn|SP>", Kind: "gp", Fields: []string{"Rn"}, Width: 64, SP: true}
	return isaEncoding{
		Name:     aarch64STP64EncodingName,
		Mnemonic: "stp",
		Mask:     0xffc00000,
		Value:    0xa9000000,
		Fields: []isaField{
			{Name: "opc", Hi: 31, Width: 2},
			{Name: "VR", Hi: 26, Width: 1},
			{Name: "L", Hi: 22, Width: 1},
			{Name: "imm7", Hi: 21, Width: 7},
			{Name: "Rt2", Hi: 14, Width: 5},
			{Name: "Rn", Hi: 9, Width: 5},
			{Name: "Rt", Hi: 4, Width: 5},
		},
		Forms: []isaForm{
			{Operands: []isaOperand{
				register("<Xt1>", "Rt"),
				register("<Xt2>", "Rt2"),
				{Sym: "[<Xn|SP>, #<imm>]", Kind: "mem", Mode: "off", Sub: []isaOperand{
					base,
					{Sym: "off", Kind: "imm", Fields: []string{"imm7"}, Min: -512, Max: 504, HasRange: true, Scale: 8},
				}},
			}},
			{Operands: []isaOperand{
				register("<Xt1>", "Rt"),
				register("<Xt2>", "Rt2"),
				{Sym: "[<Xn|SP>]", Kind: "mem", Mode: "off", Sub: []isaOperand{base}},
			}, Defaults: []isaDefault{{Field: "imm7", Value: 0}}},
		},
	}
}

func TestAArch64STP64LeanEncodingMatchesTable(t *testing.T) {
	encoding := aarch64STP64GeneratedEncoding(t)
	want := expectedAArch64STP64Encoding()
	if !reflect.DeepEqual(encoding, want) {
		t.Fatalf("generated %s row drifted:\n--- have\n%#v\n--- want\n%#v",
			aarch64STP64EncodingName, encoding, want)
	}

	path := filepath.Join("..", "spec", "lean", "Oak", "AArch64Encoding.lean")
	contents, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	encodingMatch := aarch64STP64LeanEncodingBlock.FindStringSubmatch(string(contents))
	if encodingMatch == nil {
		t.Fatalf("%s lacks its generated STP64 encoding block", path)
	}
	var leanFields []string
	for _, field := range want.Fields {
		leanFields = append(leanFields, fmt.Sprintf("⟨%q, %d, %d⟩",
			field.Name, field.Hi, field.Width))
	}
	wantEncoding := fmt.Sprintf(
		"def stp64Offset : Encoding := ⟨%q, %q, 0x%08x#32, 0x%08x#32, [%s]⟩",
		want.Name, want.Mnemonic, want.Value, want.Mask, strings.Join(leanFields, ", "))
	if got := strings.TrimSpace(encodingMatch[1]); got != wantEncoding {
		t.Fatalf("%s STP64 encoding drifted from asm/encodings_gen.go:\n--- have\n%s\n--- want\n%s",
			path, got, wantEncoding)
	}

	wordMatch := aarch64STP64LeanWordBlock.FindStringSubmatch(string(contents))
	if wordMatch == nil {
		t.Fatalf("%s lacks its exact zero-pair word block", path)
	}
	wantWordBlock := "def stpXzrXzrX0 : BitVec 32 := " +
		"encodeStp64Offset 0#7 0#5 0b11111#5 0b11111#5 " +
		"def stpXzrXzrX0Plus16 : BitVec 32 := " +
		"encodeStp64Offset 2#7 0#5 0b11111#5 0b11111#5 " +
		"theorem stp_xzr_xzr_x0_word : stpXzrXzrX0 = 0xa9007c1f#32 := by native_decide " +
		"theorem stp_xzr_xzr_x0_plus_16_word : " +
		"stpXzrXzrX0Plus16 = 0xa9017c1f#32 := by native_decide"
	if got := strings.Join(strings.Fields(wordMatch[1]), " "); got != wantWordBlock {
		t.Fatalf("%s exact zero-pair word block drifted:\n--- have\n%s\n--- want\n%s",
			path, got, wantWordBlock)
	}
}

func TestAArch64STP64ExactWordsAndBoundaries(t *testing.T) {
	tests := []struct {
		text string
		word uint32
	}{
		{stpZeroPairText, stpZeroPairWord},
		{stpZeroPairPlus16Text, stpZeroPairPlus16Word},
		{"stp xzr, xzr, [x0, #-512]", 0xa9207c1f},
		{"stp xzr, xzr, [x0, #504]", 0xa91ffc1f},
	}
	for _, test := range tests {
		got, err := encodeText(t, test.text)
		if err != nil {
			t.Fatalf("encode %q: %v", test.text, err)
		}
		if got != test.word {
			t.Fatalf("encode %q = %08x, want %08x", test.text, got, test.word)
		}
	}
	for _, text := range []string{
		"stp xzr, xzr, [x0, #-520]",
		"stp xzr, xzr, [x0, #512]",
		"stp xzr, xzr, [x0, #4]",
	} {
		if _, err := encodeText(t, text); err == nil {
			t.Errorf("encode %q succeeded outside the signed scaled imm7 range", text)
		}
	}
}

func TestAArch64STP64NearbyWordsRemainDistinct(t *testing.T) {
	for _, test := range []struct {
		text string
		word uint32
	}{
		{"stp x30, xzr, [x0]", 0xa9007c1e},
		{"stp xzr, x30, [x0]", 0xa900781f},
		{"stp xzr, xzr, [x1]", 0xa9007c3f},
		{"stp xzr, xzr, [x0, #8]", 0xa900fc1f},
		{"stp wzr, wzr, [x0]", 0x29007c1f},
		{"ldp xzr, xzr, [x0]", 0xa9407c1f},
	} {
		got, err := encodeText(t, test.text)
		if err != nil {
			t.Fatalf("encode %q: %v", test.text, err)
		}
		if got != test.word {
			t.Fatalf("encode %q = %08x, want %08x", test.text, got, test.word)
		}
		if got == stpZeroPairWord || got == stpZeroPairPlus16Word {
			t.Errorf("nearby encoding %q = %08x aliases an exact zero-pair word", test.text, got)
		}
	}
}
