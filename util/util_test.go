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
