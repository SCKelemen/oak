package evaluator

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/semir"
)

// Interpreter parity for the arm64 value-transforming instruction functions.
func TestArm64IntrinsicsInterpreterParity(t *testing.T) {
	tests := []struct {
		input string
		want  int64
	}{
		{"arm64.clz64(u64(1))", 63},
		{"arm64.clz32(u32(0))", 32},
		{"arm64.clz64(u64(0))", 64},
		{"arm64.clz64(u64(255))", 56},
		{"arm64.cnt32(u32(0))", 0},
		{"arm64.cnt32(u32(4294967295))", 32},
		{"arm64.cnt64(u64(255))", 8},
		{"arm64.cnt64(u64(18446744073709551615))", 64},
		{"arm64.rev32(u32(287454020))", 1144201745},
		{"arm64.rev32(arm64.rev32(u32(19088743)))", 19088743},
		{"arm64.rev64(arm64.rev64(u64(81985529216486895)))", 81985529216486895},
		{"arm64.rbit32(u32(1))", 2147483648},
		{"arm64.rbit64(arm64.rbit64(u64(1234567890)))", 1234567890},
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

// Architectural barriers cannot be faithfully executed by the sequential Go
// evaluator. Every source barrier must fail explicitly rather than disappear as
// a no-op or be over-strengthened into an unrelated host primitive.
func TestArm64BarriersRequireNativeAArch64Backend(t *testing.T) {
	for _, member := range semir.Arm64BarrierMembers() {
		t.Run(member, func(t *testing.T) {
			result := testEval("arm64." + member + "()")
			err, ok := result.(*object.Error)
			if !ok {
				t.Fatalf("%s: expected native-backend error, got %v", member, result)
			}
			if !strings.Contains(err.Message, "native AArch64 backend") {
				t.Fatalf("%s error %q does not explain native AArch64 requirement", member, err.Message)
			}
		})
	}
}

// Extern bindings are native-backend only: calling one under interpretation is
// a diagnosed error, never a silent no-op.
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
