package typechecker

import (
	"strings"
	"testing"
)

// The FFI boundary rules of docs/spec/92-ffi.md: extern signatures are
// c.*-only (OAK-F0101), symbols are C identifiers (OAK-F0102), c.extern is
// definition-only (OAK-F0103), conversions are the exact table rows, and
// the instruction functions are ordinary typed calls.
func TestFFIBoundaryRules(t *testing.T) {
	tests := []struct {
		name       string
		input      string
		hasError   bool
		wantInText string
	}{
		{
			"valid extern binding over c types",
			"putchar: (ch: c.Int): c.Int = c.extern(\"putchar\")",
			false, "",
		},
		{
			"valid nullary extern with unit return",
			"flush: (): () = c.extern(\"fflush_unlocked\")",
			false, "",
		},
		{
			"extern parameter must be a c type",
			"putchar: (ch: i32): c.Int = c.extern(\"putchar\")",
			true, "OAK-F0101",
		},
		{
			"extern return must be a c type or unit",
			"putchar: (ch: c.Int): i32 = c.extern(\"putchar\")",
			true, "OAK-F0101",
		},
		{
			"extern symbol must be a C identifier",
			"boom: (): () = c.extern(\"evil(); //\")",
			true, "OAK-F0102",
		},
		{
			"c.extern is not an expression",
			"fn f() -> i32 { x := c.extern(\"puts\")\n1 }",
			true, "OAK-F0103",
		},
		{
			"extern call before the binding in source order",
			"fn f() -> c.Int = putchar(c.Int(65))\nputchar: (ch: c.Int): c.Int = c.extern(\"putchar\")",
			false, "",
		},
		{
			"exact-width conversion round trip",
			"fn f() -> i32 { n: c.Int32 = c.Int32(41)\ni32(n) + 1 }",
			false, "",
		},
		{
			"untyped literals infer against the conversion operand",
			"fn f() -> c.Int64 = c.Int64(7)",
			false, "",
		},
		{
			"conversion rejects a mismatched typed operand",
			"fn f(x: u32) -> c.Int32 = c.Int32(x)",
			true, "c.Int32 converts i32 values",
		},
		{
			"no inverse for c.Size",
			"fn f(x: c.Size) -> u32 = u32(x)",
			true, "",
		},
		{
			"c types are nominal, not interchangeable",
			"fn f(x: c.Int32) -> c.Int = x",
			true, "",
		},
		{
			"no arithmetic on c types",
			"fn f(x: c.Int, y: c.Int) -> c.Int = x + y",
			true, "",
		},
		{
			"intrinsics type as ordinary functions",
			"fn f(x: u64) -> u64 = arm64.clz64(x)",
			false, "",
		},
		{
			"intrinsic operand width is enforced",
			"fn f(x: u32) -> u64 = arm64.clz64(x)",
			true, "arm64.clz64 expects u64",
		},
		{
			"unknown instruction functions are rejected",
			"fn f(x: u64) -> u64 = arm64.popcount(x)",
			true, "no instruction function",
		},
		{
			"a local named c shadows the library in expression position",
			"fn f() -> i32 { c: i32 = 1\nc + 1 }",
			false, "",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			tc := setupTypeChecker(tt.input)
			program := parseProgram(tt.input)
			tc.CheckProgram(program)

			hasError := len(tc.Errors()) > 0
			if hasError != tt.hasError {
				t.Fatalf("input %q: expected error=%v, got errors=%v", tt.input, tt.hasError, tc.Errors())
			}
			if tt.wantInText == "" {
				return
			}
			all := strings.Join(tc.Errors(), "\n")
			for _, d := range tc.Diagnostics() {
				all += "\n" + d.Code + " " + d.Message
			}
			if !strings.Contains(all, tt.wantInText) {
				t.Fatalf("diagnostics %q do not mention %q", all, tt.wantInText)
			}
		})
	}
}
