package source

import (
	"math/rand"
	"testing"
	"unicode/utf8"
)

// Boundary bytes around every bracket in the Lean model's Seq constructors.
var boundaryBytes = []byte{
	0x00, 0x7F, 0x80, 0x8F, 0x90, 0x9F, 0xA0, 0xBF, 0xC0, 0xC1, 0xC2,
	0xDF, 0xE0, 0xE1, 0xEC, 0xED, 0xEE, 0xEF, 0xF0, 0xF1, 0xF3, 0xF4, 0xF5, 0xFF,
}

// The implementation must agree with the standard library's validator on
// every input (differential check of the transliteration against an
// independent implementation).
func TestValidateUTF8MatchesStdlibExhaustively(t *testing.T) {
	// Exhaustive one- and two-byte inputs.
	for b0 := 0; b0 <= 0xFF; b0++ {
		input := string([]byte{byte(b0)})
		if _, got := ValidateUTF8(input); got != utf8.ValidString(input) {
			t.Fatalf("1-byte disagreement on %#x", b0)
		}
		for b1 := 0; b1 <= 0xFF; b1++ {
			input := string([]byte{byte(b0), byte(b1)})
			if _, got := ValidateUTF8(input); got != utf8.ValidString(input) {
				t.Fatalf("2-byte disagreement on %#x %#x", b0, b1)
			}
		}
	}

	// Three- and four-byte inputs over all leads crossed with bracket
	// boundary continuations.
	for b0 := 0; b0 <= 0xFF; b0++ {
		for _, b1 := range boundaryBytes {
			for _, b2 := range boundaryBytes {
				input := string([]byte{byte(b0), b1, b2})
				if _, got := ValidateUTF8(input); got != utf8.ValidString(input) {
					t.Fatalf("3-byte disagreement on %#x %#x %#x", b0, b1, b2)
				}
				for _, b3 := range boundaryBytes {
					input := string([]byte{byte(b0), b1, b2, b3})
					if _, got := ValidateUTF8(input); got != utf8.ValidString(input) {
						t.Fatalf("4-byte disagreement on %#x %#x %#x %#x", b0, b1, b2, b3)
					}
				}
			}
		}
	}
}

func TestValidateUTF8MatchesStdlibOnRandomInputs(t *testing.T) {
	rng := rand.New(rand.NewSource(0x0AC0FFEE))
	for trial := 0; trial < 200000; trial++ {
		length := rng.Intn(9)
		buf := make([]byte, length)
		for i := range buf {
			buf[i] = byte(rng.Intn(256))
		}
		input := string(buf)
		if _, got := ValidateUTF8(input); got != utf8.ValidString(input) {
			t.Fatalf("random disagreement on %#v", buf)
		}
	}
}

func TestValidateUTF8KnownVectors(t *testing.T) {
	valid := []string{
		"",
		"hello",
		"héllo",      // 2-byte
		"€",          // euro, 3-byte
		"世界",         // CJK
		"\U0001F600", // emoji, 4-byte
		"�",          // replacement char itself is valid
		"\U0010FFFF", // maximum scalar
		"퟿",         // brackets around the surrogate gap
	}
	for _, input := range valid {
		if offset, ok := ValidateUTF8(input); !ok {
			t.Fatalf("valid input rejected at offset %d: %q", offset, input)
		}
	}

	invalid := []struct {
		name  string
		input string
	}{
		{"stray continuation", "\x80"},
		{"overlong 2-byte", "\xC0\xAF"},
		{"overlong 3-byte", "\xE0\x80\xAF"},
		{"overlong 4-byte", "\xF0\x8F\xBF\xBF"},
		{"surrogate", "\xED\xA0\x80"},
		{"beyond max scalar", "\xF4\x90\x80\x80"},
		{"truncated 3-byte", "\xE2\x82"},
		{"truncated 4-byte", "\xF0\x9F\x98"},
		{"invalid lead F5", "\xF5\x80\x80\x80"},
		{"invalid byte FF", "hi\xFFthere"},
	}
	for _, tc := range invalid {
		t.Run(tc.name, func(t *testing.T) {
			offset, ok := ValidateUTF8(tc.input)
			if ok {
				t.Fatalf("invalid input accepted: %q", tc.input)
			}
			if offset < 0 || offset >= len(tc.input) {
				t.Fatalf("offset %d out of range for %q", offset, tc.input)
			}
		})
	}

	// The reported offset names the first invalid sequence.
	if offset, ok := ValidateUTF8("hi\xFFthere"); ok || offset != 2 {
		t.Fatalf("offset = %d, want 2", offset)
	}
}
