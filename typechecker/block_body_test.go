package typechecker

import "testing"

// Function block bodies retain every statement (ast.BlockExpression), so
// non-final statements are type checked instead of being silently discarded.
func TestBlockBodyStatementsAreTypeChecked(t *testing.T) {
	tests := []struct {
		name     string
		input    string
		hasError bool
	}{
		{
			"well-typed local then result",
			"fn f() -> i32 { x: i32 = 1\nx }",
			false,
		},
		{
			"ill-typed non-final local is caught",
			"fn f() -> i32 { x: i32 = \"hello\"\nx }",
			true,
		},
		{
			"result type comes from the trailing expression",
			"fn f() -> string { x: i32 = 1\nx }",
			true,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			tc := setupTypeChecker(tt.input)
			program := parseProgram(tt.input)
			tc.CheckProgram(program)

			hasError := len(tc.Errors()) > 0
			if hasError != tt.hasError {
				t.Errorf("input %q: expected error=%v, got errors=%v", tt.input, tt.hasError, tc.Errors())
			}
		})
	}
}
