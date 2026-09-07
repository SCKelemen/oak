package typechecker

import (
	"strings"
	"testing"
)

// A packed record places fields densely, so an Atomic[T] field can land
// unaligned — misaligned C11 _Atomic access is undefined behavior. The
// declaration is rejected at the type level (and the backend fails closed
// independently).
func TestPackedRecordRejectsAtomicStorage(t *testing.T) {
	input := "Bad: type = struct(packed) {\n  tag: u8\n  cell: Atomic[u32]\n}\n"
	tc := setupTypeChecker(input)
	program := parseProgram(input)
	tc.CheckProgram(program)
	joined := strings.Join(tc.Errors(), "\n")
	if !strings.Contains(joined, "packed records cannot contain atomic storage") {
		t.Fatalf("packed atomic field must be rejected, got errors: %v", tc.Errors())
	}
}

// The same shape without packing is legal — the rejection is about density,
// not about atomics in records.
func TestNaturalRecordAcceptsAtomicStorage(t *testing.T) {
	input := "Fine: type = struct {\n  tag: u8\n  cell: Atomic[u32]\n}\n"
	tc := setupTypeChecker(input)
	program := parseProgram(input)
	tc.CheckProgram(program)
	if len(tc.Errors()) > 0 {
		t.Fatalf("unexpected errors: %v", tc.Errors())
	}
}

// Per-field align inside a packed container contradicts dense placement.
func TestPackedRecordRejectsFieldAlignment(t *testing.T) {
	input := "Bad: type = struct(packed) {\n  a(align: 4): u8\n  b: u8\n}\n"
	tc := setupTypeChecker(input)
	program := parseProgram(input)
	tc.CheckProgram(program)
	joined := strings.Join(tc.Errors(), "\n")
	if !strings.Contains(joined, "packing and raised member alignment contradict") {
		t.Fatalf("field align in packed record must be rejected, got: %v", tc.Errors())
	}
}
