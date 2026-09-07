package typechecker

import (
	"strings"
	"testing"
)

// Statement-position conditionals through the ? match sugar and Boolean
// connectives (docs/spec/10-syntax.md §3a): Bool-typed conditions and
// operands, both branches checked. There are no if/else keywords.
func TestIfStatementsAndLogicalOperators(t *testing.T) {
	tests := []struct {
		name       string
		input      string
		hasError   bool
		wantInText string
	}{
		{
			"condition sugar with both block branches",
			"f: (n: i32): i32 {\n  r: i32 = 0\n  n < 0 ? {\n    r = 1\n  } | {\n    r = 2\n  }\n  r\n}",
			false, "",
		},
		{
			"one-armed condition statement",
			"f: (n: i32): i32 {\n  r: i32 = 0\n  n < 0 ? {\n    r = 1\n  }\n  r\n}",
			false, "",
		},
		{
			"explicit true/false pattern arms",
			"f: (a: Bool): i32 = a ?\n  | true => 1\n  | false => 2",
			false, "",
		},
		{
			"positional expression branches",
			"f: (a: Bool): i32 = a ? 1 | 2",
			false, "",
		},
		{
			"condition must be Bool",
			"f: (n: i32): i32 {\n  n ? {\n    n = 0\n  }\n  n\n}",
			true, "",
		},
		{
			"branch bodies are checked",
			"f: (n: i32): i32 {\n  n < 0 ? {\n    x: i32 = \"nope\"\n  }\n  n\n}",
			true, "",
		},
		{
			"short-circuit connectives type as Bool",
			"f: (a, b: Bool): Bool = a && (b || !a)",
			false, "",
		},
		{
			"connective operands must be Bool",
			"f: (a: Bool, n: i32): Bool = a && n",
			true, "requires Bool operands",
		},
		{
			"record fields as connective operands",
			"Flags: type = struct {\n  a: Bool\n  b: Bool\n}\n\nf: (s: Flags): Bool = s.a || s.b",
			false, "",
		},
		{
			"bits reinterpretation requires same width and opposite sign",
			"f: (x: u32): i32 = i32_bits_u32(x)",
			false, "",
		},
		{
			"bits rejects width changes",
			"f: (x: u32): i64 = i64_bits_u32(x)",
			true, "requires the same width",
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			tc := setupTypeChecker(tt.input)
			program := parseProgram(tt.input)
			tc.CheckProgram(program)
			hasError := len(tc.Errors()) > 0
			if hasError != tt.hasError {
				t.Fatalf("expected error=%v, got %v", tt.hasError, tc.Errors())
			}
			if tt.wantInText != "" && !strings.Contains(strings.Join(tc.Errors(), "\n"), tt.wantInText) {
				t.Fatalf("errors %v do not mention %q", tc.Errors(), tt.wantInText)
			}
		})
	}
}
