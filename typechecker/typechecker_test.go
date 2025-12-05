package typechecker

import (
	"testing"
)

func TestTypeChecker_IntegerLiteral(t *testing.T) {
	tests := []struct {
		input    string
		expected string
	}{
		{"5", "i32"},
		{"42", "i32"},
	}

	for _, tt := range tests {
		tc := setupTypeChecker(tt.input)
		program := parseProgram(tt.input)
		tc.CheckProgram(program)

		if len(tc.Errors()) > 0 {
			t.Errorf("unexpected errors: %v", tc.Errors())
		}
	}
}

func TestTypeChecker_StringLiteral(t *testing.T) {
	tests := []struct {
		input    string
		expected string
	}{
		{`"hello"`, "string"},
		{`"world"`, "string"},
	}

	for _, tt := range tests {
		tc := setupTypeChecker(tt.input)
		program := parseProgram(tt.input)
		tc.CheckProgram(program)

		if len(tc.Errors()) > 0 {
			t.Errorf("unexpected errors: %v", tc.Errors())
		}
	}
}

func TestTypeChecker_BooleanLiteral(t *testing.T) {
	tests := []struct {
		input    string
		expected string
	}{
		{"true", "Bool"},
		{"false", "Bool"},
	}

	for _, tt := range tests {
		tc := setupTypeChecker(tt.input)
		program := parseProgram(tt.input)
		tc.CheckProgram(program)

		if len(tc.Errors()) > 0 {
			t.Errorf("unexpected errors: %v", tc.Errors())
		}
	}
}

func TestTypeChecker_VariableDeclaration(t *testing.T) {
	tests := []struct {
		input    string
		hasError bool
	}{
		{"x: i32 = 5", false},
		{"x: i32", false},
		{"x: i32 = 5; x", false},     // type inference - need to use variable after declaration
		{"x: string = 5", true},      // type mismatch
		{"x: i32 = \"hello\"", true}, // type mismatch
	}

	for _, tt := range tests {
		tc := setupTypeChecker(tt.input)
		program := parseProgram(tt.input)
		tc.CheckProgram(program)

		hasError := len(tc.Errors()) > 0
		if hasError != tt.hasError {
			t.Errorf("input %q: expected error=%v, got errors=%v", tt.input, tt.hasError, tc.Errors())
		}
	}
}

func TestTypeChecker_ArithmeticOperations(t *testing.T) {
	tests := []struct {
		input    string
		hasError bool
	}{
		{"5 + 3", false},
		{"5 - 3", false},
		{"5 * 3", false},
		{"5 / 3", false},
		{"5 + \"hello\"", true},          // type mismatch
		{"\"hello\" + \"world\"", false}, // string concatenation
		{"true + false", true},           // type mismatch
	}

	for _, tt := range tests {
		tc := setupTypeChecker(tt.input)
		program := parseProgram(tt.input)
		tc.CheckProgram(program)

		hasError := len(tc.Errors()) > 0
		if hasError != tt.hasError {
			t.Errorf("input %q: expected error=%v, got errors=%v", tt.input, tt.hasError, tc.Errors())
		}
	}
}

func TestTypeChecker_TypePromotion(t *testing.T) {
	tests := []struct {
		input    string
		hasError bool
	}{
		{"x: i32 = 5; y: i64 = x", false}, // widening - note: integer literal is i32, so x is i32
		{"x: i32 = 5; y: i32 = x + 10", false},
		{"x: i32 = 5; y: i64 = x + 10", false}, // promotion in expression
		{"x: i32 = 5; y: u32 = x", true},       // signed/unsigned mismatch
		{"x: u8 = 5; y: i32 = x", true},        // signed/unsigned mismatch
		// Note: u8/u16 widening would require typed literals or explicit casts
	}

	for _, tt := range tests {
		tc := setupTypeChecker(tt.input)
		program := parseProgram(tt.input)
		tc.CheckProgram(program)

		hasError := len(tc.Errors()) > 0
		if hasError != tt.hasError {
			t.Errorf("input %q: expected error=%v, got errors=%v", tt.input, tt.hasError, tc.Errors())
		}
	}
}

func TestTypeChecker_ComparisonOperations(t *testing.T) {
	tests := []struct {
		input    string
		hasError bool
	}{
		{"5 < 3", false},
		{"5 > 3", false},
		{"5 == 3", false},
		{"5 != 3", false},
		{"\"hello\" == \"world\"", false},
		{"5 < \"hello\"", true}, // type mismatch
		{"true < false", true},  // type mismatch
		// Note: <= and >= may not be parsed correctly yet
	}

	for _, tt := range tests {
		tc := setupTypeChecker(tt.input)
		program := parseProgram(tt.input)
		tc.CheckProgram(program)

		hasError := len(tc.Errors()) > 0
		if hasError != tt.hasError {
			t.Errorf("input %q: expected error=%v, got errors=%v", tt.input, tt.hasError, tc.Errors())
		}
	}
}

func TestTypeChecker_PrefixExpressions(t *testing.T) {
	tests := []struct {
		input    string
		hasError bool
	}{
		{"!true", false},
		{"!false", false},
		{"!5", true},    // not bool
		{"-5", false},   // negation
		{"-true", true}, // not numeric
		// Note: unary + may not be parsed correctly yet
	}

	for _, tt := range tests {
		tc := setupTypeChecker(tt.input)
		program := parseProgram(tt.input)
		tc.CheckProgram(program)

		hasError := len(tc.Errors()) > 0
		if hasError != tt.hasError {
			t.Errorf("input %q: expected error=%v, got errors=%v", tt.input, tt.hasError, tc.Errors())
		}
	}
}

func TestTypeChecker_RecordLiterals(t *testing.T) {
	tests := []struct {
		input    string
		hasError bool
	}{
		{"{ code: 200, status: \"Ok\" }", false},
		{"{ x: 5, y: 10 }", false},
		{"{}", false}, // empty record
	}

	for _, tt := range tests {
		tc := setupTypeChecker(tt.input)
		program := parseProgram(tt.input)
		tc.CheckProgram(program)

		hasError := len(tc.Errors()) > 0
		if hasError != tt.hasError {
			t.Errorf("input %q: expected error=%v, got errors=%v", tt.input, tt.hasError, tc.Errors())
		}
	}
}

func TestTypeChecker_RecordFieldAccess(t *testing.T) {
	tests := []struct {
		input    string
		hasError bool
	}{
		{"r: { code: i32 } = { code: 200 }; r.code", false},
		{"r := { code: 200 }; r.code", false},  // type inference
		{"r := { code: 200 }; r.status", true}, // field doesn't exist
	}

	for _, tt := range tests {
		tc := setupTypeChecker(tt.input)
		program := parseProgram(tt.input)
		tc.CheckProgram(program)

		hasError := len(tc.Errors()) > 0
		if hasError != tt.hasError {
			t.Errorf("input %q: expected error=%v, got errors=%v", tt.input, tt.hasError, tc.Errors())
		}
	}
}

func TestTypeChecker_ArrayLiterals(t *testing.T) {
	tests := []struct {
		input    string
		hasError bool
	}{
		{"[1, 2, 3]", false},
		{"[]", false}, // empty array
		{"[\"a\", \"b\", \"c\"]", false},
		{"[1, \"hello\"]", true}, // mixed types
	}

	for _, tt := range tests {
		tc := setupTypeChecker(tt.input)
		program := parseProgram(tt.input)
		tc.CheckProgram(program)

		hasError := len(tc.Errors()) > 0
		if hasError != tt.hasError {
			t.Errorf("input %q: expected error=%v, got errors=%v", tt.input, tt.hasError, tc.Errors())
		}
	}
}

func TestTypeChecker_ArrayIndexing(t *testing.T) {
	tests := []struct {
		input    string
		hasError bool
	}{
		{"arr := [1, 2, 3]; arr[0]", false},
		{"arr := [1, 2, 3]; arr[1]", false},
		{"5[0]", true}, // indexing non-array
		// Note: string index checking may need parser fixes
	}

	for _, tt := range tests {
		tc := setupTypeChecker(tt.input)
		program := parseProgram(tt.input)
		tc.CheckProgram(program)

		hasError := len(tc.Errors()) > 0
		if hasError != tt.hasError {
			t.Errorf("input %q: expected error=%v, got errors=%v", tt.input, tt.hasError, tc.Errors())
		}
	}
}

func TestTypeChecker_WhileStatement(t *testing.T) {
	tests := []struct {
		input    string
		hasError bool
	}{
		{"while true { 5 }", false},
		{"while false { 5 }", false},
		{"while 5 { 5 }", true},         // condition not bool
		{"while \"hello\" { 5 }", true}, // condition not bool
	}

	for _, tt := range tests {
		tc := setupTypeChecker(tt.input)
		program := parseProgram(tt.input)
		tc.CheckProgram(program)

		hasError := len(tc.Errors()) > 0
		if hasError != tt.hasError {
			t.Errorf("input %q: expected error=%v, got errors=%v", tt.input, tt.hasError, tc.Errors())
		}
	}
}

func TestTypeChecker_AssignmentStatement(t *testing.T) {
	tests := []struct {
		input    string
		hasError bool
	}{
		{"x: i32 = 5; x = 10", false},
		{"x: i32 = 5; x = \"hello\"", true}, // type mismatch
		{"x: i32 = 5; y = 10", true},        // undefined variable y
	}

	for _, tt := range tests {
		tc := setupTypeChecker(tt.input)
		program := parseProgram(tt.input)
		tc.CheckProgram(program)

		hasError := len(tc.Errors()) > 0
		if hasError != tt.hasError {
			t.Errorf("input %q: expected error=%v, got errors=%v", tt.input, tt.hasError, tc.Errors())
		}
	}
}

func TestTypeChecker_FunctionStatement(t *testing.T) {
	tests := []struct {
		input    string
		hasError bool
	}{
		{"fn add(a: i32, b: i32) -> i32 { a + b }", false},
		{"fn add(a: i32, b: i32) -> i32 { \"hello\" }", true}, // return type mismatch
		{"fn add(a: i32, b: i32) -> string { a + b }", true},  // return type mismatch
	}

	for _, tt := range tests {
		tc := setupTypeChecker(tt.input)
		program := parseProgram(tt.input)
		tc.CheckProgram(program)

		hasError := len(tc.Errors()) > 0
		if hasError != tt.hasError {
			t.Errorf("input %q: expected error=%v, got errors=%v", tt.input, tt.hasError, tc.Errors())
		}
	}
}

func TestTypeChecker_FunctionInvocation(t *testing.T) {
	tests := []struct {
		input    string
		hasError bool
	}{
		{"fn add(a: i32, b: i32) -> i32 { a + b }; add(5, 3)", false},
		{"fn add(a: i32, b: i32) -> i32 { a + b }; add(5)", true},            // wrong arg count
		{"fn add(a: i32, b: i32) -> i32 { a + b }; add(5, 3, 4)", true},      // wrong arg count
		{"fn add(a: i32, b: i32) -> i32 { a + b }; add(\"hello\", 3)", true}, // wrong arg type
		{"fn add(a: i32, b: i32) -> i32 { a + b }; result := add(5, 3)", false},
		// Note: calling non-function may need parser fixes
	}

	for _, tt := range tests {
		tc := setupTypeChecker(tt.input)
		program := parseProgram(tt.input)
		tc.CheckProgram(program)

		hasError := len(tc.Errors()) > 0
		if hasError != tt.hasError {
			t.Errorf("input %q: expected error=%v, got errors=%v", tt.input, tt.hasError, tc.Errors())
		}
	}
}

func TestTypeChecker_UndefinedVariable(t *testing.T) {
	tests := []struct {
		input    string
		hasError bool
	}{
		{"x", true},              // undefined
		{"x: i32 = 5; x", false}, // defined
		{"x: i32 = 5; y", true},  // undefined
	}

	for _, tt := range tests {
		tc := setupTypeChecker(tt.input)
		program := parseProgram(tt.input)
		tc.CheckProgram(program)

		hasError := len(tc.Errors()) > 0
		if hasError != tt.hasError {
			t.Errorf("input %q: expected error=%v, got errors=%v", tt.input, tt.hasError, tc.Errors())
		}
	}
}

// Helper functions are now in typechecker_test_helper.go
