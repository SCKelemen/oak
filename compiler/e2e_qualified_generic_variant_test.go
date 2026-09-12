package compiler

import (
	"strings"
	"testing"
)

// A type-qualified construction of a generic ADT — `Box.Full(x)` for
// `Box[T]` — named the template's constructor in C (`oak_Box_Full`), which
// does not exist; only the instantiation's does (`oak_Box_u32_Full`). The
// backend now takes the checker's recorded resolution for the qualified
// form as it already did for the bare `.Full(x)`, so both spellings agree
// (docs/spec/30-adts-patterns.md; compiler/variants.go).
func TestE2EQualifiedGenericVariantConstruction(t *testing.T) {
	program := `Box[T]: type = Full: T | Empty

peek: (b: Box[u32], x: u32): u32 = b ? | .Full(v) => x + v | .Empty => x

main: (): i32 {
  qualified: Box[u32] = Box.Full(u32(30))
  bare: Box[u32] = .Full(u32(30))
  empty: Box[u32] = Box.Empty
  i32_bits_u32(peek(qualified, u32(6)) + peek(bare, u32(6)) - peek(empty, u32(30)))
}
`
	output, err := New().WithSource("qualified.oak", program).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	if strings.Contains(output, "oak_Box_Full(") || strings.Contains(output, "oak_Box_Empty(") {
		t.Fatalf("qualified construction named the template's constructor:\n%s", output)
	}
	if !strings.Contains(output, "oak_Box_u32_Full(") {
		t.Fatalf("instantiation constructor missing:\n%s", output)
	}
	code, abnormal := buildAndRun(t, "qualified", program)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
