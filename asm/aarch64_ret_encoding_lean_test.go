package asm

import (
	"bytes"
	"fmt"
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
)

const (
	aarch64RetEncodingName = "RET_64R_branch_reg"
	aarch64RetWord         = uint32(0xd65f03c0)
)

var aarch64RetFields = []isaField{
	{Name: "Z", Hi: 24, Width: 1},
	{Name: "op", Hi: 22, Width: 2},
	{Name: "op2", Hi: 20, Width: 5},
	{Name: "A", Hi: 11, Width: 1},
	{Name: "M", Hi: 10, Width: 1},
	{Name: "Rn", Hi: 9, Width: 5},
	{Name: "Rm", Hi: 4, Width: 5},
}

var aarch64RetEncodingBlock = regexp.MustCompile(`(?s)-- OAK-A64-RET-ENC-BEGIN[^\n]*\n(.*?)-- OAK-A64-RET-ENC-END`)
var aarch64RetWordBlock = regexp.MustCompile(`(?s)-- OAK-A64-RET-WORD-BEGIN[^\n]*\n(.*?)-- OAK-A64-RET-WORD-END`)

func aarch64RetEncoding(t *testing.T) isaEncoding {
	t.Helper()
	var matches []isaEncoding
	for _, enc := range isaEncodings {
		if enc.Name == aarch64RetEncodingName {
			matches = append(matches, enc)
		}
	}
	if len(matches) != 1 {
		t.Fatalf("generated AArch64 table has %d %s rows, want one", len(matches), aarch64RetEncodingName)
	}
	return matches[0]
}

func aarch64RetLeanLine(enc isaEncoding) string {
	fields := make([]string, 0, len(enc.Fields))
	for _, field := range enc.Fields {
		fields = append(fields, fmt.Sprintf("⟨%q, %d, %d⟩", field.Name, field.Hi, field.Width))
	}
	return fmt.Sprintf("def ret : Encoding := ⟨%q, %q, 0x%08x#32, 0x%08x#32, [%s]⟩",
		enc.Name, enc.Mnemonic, enc.Value, enc.Mask, strings.Join(fields, ", "))
}

func aarch64RetBlockLines(block string) []string {
	var lines []string
	for _, line := range strings.Split(block, "\n") {
		line = strings.TrimSpace(line)
		if strings.HasPrefix(line, "def ") || strings.HasPrefix(line, "theorem ") {
			lines = append(lines, line)
		}
	}
	return lines
}

func TestAArch64ReturnLeanEncodingMatchesTable(t *testing.T) {
	enc := aarch64RetEncoding(t)
	if enc.Mnemonic != "ret" || enc.Mask != 0xfffffc1f || enc.Value != 0xd65f0000 {
		t.Fatalf("generated RET row is %s mask=%#08x value=%#08x", enc.Mnemonic, enc.Mask, enc.Value)
	}
	if len(enc.Fields) != len(aarch64RetFields) {
		t.Fatalf("generated RET fields = %+v, want %+v", enc.Fields, aarch64RetFields)
	}
	for i, want := range aarch64RetFields {
		if enc.Fields[i] != want {
			t.Fatalf("generated RET field %d = %+v, want %+v", i, enc.Fields[i], want)
		}
	}
	if len(enc.Forms) != 2 {
		t.Fatalf("generated RET forms = %+v, want explicit Xn and operandless default", enc.Forms)
	}
	explicit := enc.Forms[0]
	if len(explicit.Operands) != 1 || len(explicit.Defaults) != 0 {
		t.Fatalf("generated explicit RET form = %+v", explicit)
	}
	xn := explicit.Operands[0]
	if xn.Sym != "<Xn>" || xn.Kind != "gp" || len(xn.Fields) != 1 ||
		xn.Fields[0] != "Rn" || xn.Width != 64 || !xn.ZR || xn.SP {
		t.Fatalf("generated explicit RET operand = %+v", xn)
	}
	defaultForm := enc.Forms[1]
	if len(defaultForm.Operands) != 0 || len(defaultForm.Defaults) != 1 ||
		defaultForm.Defaults[0].Field != "Rn" || defaultForm.Defaults[0].Value != 30 {
		t.Fatalf("generated operandless RET form = %+v", defaultForm)
	}

	path := filepath.Join("..", "spec", "lean", "Oak", "AArch64ReturnEncoding.lean")
	contents, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	encodingMatch := aarch64RetEncodingBlock.FindStringSubmatch(string(contents))
	if encodingMatch == nil {
		t.Fatalf("%s lacks its generated RET-encoding block", path)
	}
	gotEncoding := aarch64RetBlockLines(encodingMatch[1])
	wantEncoding := []string{aarch64RetLeanLine(enc)}
	if strings.Join(gotEncoding, "\n") != strings.Join(wantEncoding, "\n") {
		t.Fatalf("%s drifted from asm/encodings_gen.go:\n--- have\n%s\n--- want\n%s",
			path, strings.Join(gotEncoding, "\n"), strings.Join(wantEncoding, "\n"))
	}
	wordMatch := aarch64RetWordBlock.FindStringSubmatch(string(contents))
	if wordMatch == nil {
		t.Fatalf("%s lacks its exact RET-word block", path)
	}
	wantWords := []string{
		"def encodeRetRn (rn : BitVec 5) : BitVec 32 := (ret.value &&& ret.mask) ||| (rn.setWidth 32 <<< 5)",
		"def retX30 : BitVec 32 := encodeRetRn 0b11110#5",
		"theorem ret_x30_word : retX30 = 0xd65f03c0#32 := by native_decide",
	}
	gotWords := aarch64RetBlockLines(wordMatch[1])
	if strings.Join(gotWords, "\n") != strings.Join(wantWords, "\n") {
		t.Fatalf("%s exact RET word/formula drifted:\n--- have\n%s\n--- want\n%s",
			path, strings.Join(gotWords, "\n"), strings.Join(wantWords, "\n"))
	}
}

func TestAArch64ReturnExactWords(t *testing.T) {
	tests := []struct {
		text string
		word uint32
	}{
		{text: "ret", word: aarch64RetWord},
		{text: "ret x30", word: aarch64RetWord},
		{text: "ret x0", word: 0xd65f0000},
	}
	for _, test := range tests {
		t.Run(strings.ReplaceAll(test.text, " ", "_"), func(t *testing.T) {
			word, err := encodeText(t, test.text)
			if err != nil {
				t.Fatalf("encode %q: %v", test.text, err)
			}
			if word != test.word {
				t.Fatalf("encode %q = %#08x, want %#08x", test.text, word, test.word)
			}
		})
	}
}

func TestAArch64ReturnFunctionExactBytes(t *testing.T) {
	unit, errs := ParseUnit("ret_word.arm64.oakasm", "ret_word: () -> () = {\n  ret\n}\n")
	if len(errs) != 0 || unit == nil || len(unit.Functions) != 1 {
		t.Fatalf("parse one-instruction RET function: %v", errs)
	}
	code, relocs, err := EncodeFunction(unit.Functions[0])
	if err != nil {
		t.Fatal(err)
	}
	if len(relocs) != 0 {
		t.Fatalf("RET emitted relocations: %+v", relocs)
	}
	want := []byte{0xc0, 0x03, 0x5f, 0xd6}
	if !bytes.Equal(code, want) {
		t.Fatalf("RET bytes = %x, want %x", code, want)
	}
}
