package asm

import (
	"fmt"
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
)

var aarch64BarrierEncodingNames = []string{
	"DMB_BO_barriers",
	"DSB_BO_barriers",
	"ISB_BI_barriers",
}

func aarch64BarrierLeanLine(enc isaEncoding) string {
	fields := make([]string, 0, len(enc.Fields))
	for _, field := range enc.Fields {
		if field.Name == "CRm" {
			fields = append(fields, fmt.Sprintf("⟨%q, %d, %d⟩", field.Name, field.Hi, field.Width))
		}
	}
	return fmt.Sprintf("def %s : Encoding := ⟨%q, %q, 0x%08x#32, 0x%08x#32, [%s]⟩",
		enc.Mnemonic, enc.Name, enc.Mnemonic, enc.Value, enc.Mask, strings.Join(fields, ", "))
}

var aarch64BarrierLeanBlock = regexp.MustCompile(`(?s)-- OAK-A64-BARRIER-ENC-BEGIN[^\n]*\n(.*?)-- OAK-A64-BARRIER-ENC-END`)
var aarch64BarrierWordBlock = regexp.MustCompile(`(?s)-- OAK-A64-BARRIER-WORD-BEGIN[^\n]*\n(.*?)-- OAK-A64-BARRIER-WORD-END`)

var aarch64BarrierWords = []struct {
	theorem string
	value   string
	text    string
	word    uint32
}{
	{"dmb_ishld_word", "dmbIshld", "dmb ishld", 0xd50339bf},
	{"dmb_ish_word", "dmbIsh", "dmb ish", 0xd5033bbf},
	{"dmb_sy_word", "dmbSy", "dmb sy", 0xd5033fbf},
	{"dsb_ish_word", "dsbIsh", "dsb ish", 0xd5033b9f},
	{"dsb_sy_word", "dsbSy", "dsb sy", 0xd5033f9f},
	{"isb_word", "isbSy", "isb", 0xd5033fdf},
}

func TestAArch64BarrierLeanEncodingsMatchTable(t *testing.T) {
	byName := make(map[string]isaEncoding)
	for _, enc := range isaEncodings {
		byName[enc.Name] = enc
	}
	var expected []string
	for _, name := range aarch64BarrierEncodingNames {
		enc, ok := byName[name]
		if !ok {
			t.Fatalf("generated AArch64 table lacks %s", name)
		}
		expected = append(expected, aarch64BarrierLeanLine(enc))
	}

	path := filepath.Join("..", "spec", "lean", "Oak", "AArch64Encoding.lean")
	contents, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	match := aarch64BarrierLeanBlock.FindStringSubmatch(string(contents))
	if match == nil {
		t.Fatalf("%s lacks its generated barrier-encoding block", path)
	}
	var got []string
	for _, line := range strings.Split(match[1], "\n") {
		if strings.HasPrefix(strings.TrimSpace(line), "def ") {
			got = append(got, strings.TrimSpace(line))
		}
	}
	if strings.Join(got, "\n") != strings.Join(expected, "\n") {
		t.Fatalf("%s drifted from asm/encodings_gen.go:\n--- have\n%s\n--- want\n%s",
			path, strings.Join(got, "\n"), strings.Join(expected, "\n"))
	}

	wordMatch := aarch64BarrierWordBlock.FindStringSubmatch(string(contents))
	if wordMatch == nil {
		t.Fatalf("%s lacks its exact barrier-word block", path)
	}
	var expectedWords []string
	for _, word := range aarch64BarrierWords {
		expectedWords = append(expectedWords, fmt.Sprintf(
			"theorem %s : %s = 0x%08x#32 := by native_decide",
			word.theorem, word.value, word.word))
	}
	var gotWords []string
	for _, line := range strings.Split(wordMatch[1], "\n") {
		if strings.HasPrefix(strings.TrimSpace(line), "theorem ") {
			gotWords = append(gotWords, strings.TrimSpace(line))
		}
	}
	if strings.Join(gotWords, "\n") != strings.Join(expectedWords, "\n") {
		t.Fatalf("%s exact words drifted from the AArch64 encoder contract:\n--- have\n%s\n--- want\n%s",
			path, strings.Join(gotWords, "\n"), strings.Join(expectedWords, "\n"))
	}
}

func TestAArch64BarrierExactWords(t *testing.T) {
	for _, tc := range aarch64BarrierWords {
		t.Run(strings.ReplaceAll(tc.text, " ", "_"), func(t *testing.T) {
			got, err := encodeText(t, tc.text)
			if err != nil {
				t.Fatalf("encode %q: %v", tc.text, err)
			}
			if got != tc.word {
				t.Fatalf("encode %q = %08x, want %08x", tc.text, got, tc.word)
			}
		})
	}
}
