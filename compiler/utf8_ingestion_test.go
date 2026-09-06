package compiler

import (
	"strings"
	"testing"
)

// Source ingestion validates UTF-8 (docs/spec/70-strings.md section 8): a
// string literal therefore can never carry invalid bytes into `string`
// values or generated C.
func TestParseRejectsInvalidUTF8Source(t *testing.T) {
	src := "x: string = \"bad\xFFbyte\"\n"
	_, err := New().WithSource("bad.oak", src).Parse().Get()
	if err == nil {
		t.Fatal("source with invalid UTF-8 must be rejected at ingestion")
	}
	if !strings.Contains(err.Error(), "not valid UTF-8") || !strings.Contains(err.Error(), "byte offset") {
		t.Fatalf("rejection must name the problem and byte offset, got: %v", err)
	}
}

func TestParseAcceptsMultiByteUTF8Source(t *testing.T) {
	src := "greeting: string = \"héllo 世界 \U0001F600\"\n"
	tree, err := New().WithSource("ok.oak", src).Parse().Get()
	if err != nil {
		t.Fatalf("valid multi-byte UTF-8 source must parse: %v", err)
	}
	if tree == nil || tree.Root == nil {
		t.Fatal("expected a parsed program")
	}
}
