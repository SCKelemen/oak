package util

import (
	"testing"
)

func TestDotNotIdentifierChar(t *testing.T) {
	if IsIdentifierChar('.') {
		t.Fatalf("Character '.' is an identifier char, and should not be")
	}
}

func TestUnicodeIdentifierChar(t *testing.T) {
	if !IsIdentifierInitialChar('变') {
		t.Fatalf("Character '变' should be a valid identifier initial char")
	}
	if !IsIdentifierChar('量') {
		t.Fatalf("Character '量' should be a valid identifier char")
	}
}

func TestDigitValue(t *testing.T) {
	tests := []struct {
		r    rune
		want int
		ok   bool
	}{
		{'5', 5, true},
		{'٣', 3, true},
		{'९', 9, true},
		{'A', 0, false},
	}

	for _, tt := range tests {
		got, ok := DigitValue(tt.r)
		if ok != tt.ok || got != tt.want {
			t.Fatalf("DigitValue(%q) = (%d, %t), want (%d, %t)", tt.r, got, ok, tt.want, tt.ok)
		}
	}
}

func TestNormalizeDigits(t *testing.T) {
	input := "१२३abc٤٥"
	want := "123abc45"
	got := NormalizeDigits(input)
	if got != want {
		t.Fatalf("NormalizeDigits(%q) = %q, want %q", input, got, want)
	}
}
