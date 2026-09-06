package evaluator

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/object"
)

// Interpreter parity for the arm64 instruction functions
// (docs/spec/92-ffi.md section 4): the interpreter is the third witness of
// the intrinsic semantics, alongside the instruction and portable C
// lowerings, and must agree on the Oak.Intrinsics laws.
func TestArm64IntrinsicsInterpreterParity(t *testing.T) {
	tests := []struct {
		input string
		want  int64
	}{
		{"arm64.clz64(u64(1))", 63},
		{"arm64.clz32(u32(0))", 32},   // total: CLZ(0) = width
		{"arm64.clz64(u64(0))", 64},   // total: CLZ(0) = width
		{"arm64.clz64(u64(255))", 56},
		{"arm64.rev32(u32(287454020))", 1144201745},   // 0x11223344 -> 0x44332211
		{"arm64.rev32(arm64.rev32(u32(19088743)))", 19088743},   // involution
		{"arm64.rev64(arm64.rev64(u64(81985529216486895)))", 81985529216486895},
		{"arm64.rbit32(u32(1))", 2147483648}, // bit 0 -> bit 31
		{"arm64.rbit64(arm64.rbit64(u64(1234567890)))", 1234567890}, // involution
	}
	for _, tt := range tests {
		result := testEval(tt.input)
		integer, ok := result.(*object.Integer)
		if !ok {
			t.Fatalf("%s: expected integer, got %v", tt.input, result)
		}
		if integer.Value != tt.want {
			t.Fatalf("%s = %d, want %d", tt.input, integer.Value, tt.want)
		}
	}
}

// Extern bindings are native-backend only: calling one under interpretation
// is a diagnosed error, never a silent no-op (docs/spec/92-ffi.md section 4).
func TestExternBindingsNotCallableInInterpreter(t *testing.T) {
	result := testEval(`
putchar: (ch: c.Int): c.Int = c.extern("putchar")
putchar(c.Int(65))
`)
	err, ok := result.(*object.Error)
	if !ok {
		t.Fatalf("expected error, got %v", result)
	}
	if !strings.Contains(err.Message, "native backend") {
		t.Fatalf("error %q does not explain the native-backend requirement", err.Message)
	}
}
