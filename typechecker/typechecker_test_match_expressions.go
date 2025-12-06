package typechecker

import (
	"testing"

	"github.com/SCKelemen/oak/ast"
)

// TestMatchExpression_Exhaustiveness tests that match expressions are exhaustive
func TestMatchExpression_Exhaustiveness(t *testing.T) {
	tests := []struct {
		name     string
		input    string
		hasError bool
	}{
		{
			"exhaustive match on bool",
			`x: Bool = true; x ? | true -> 1 | false -> 0`,
			false,
		},
		{
			"non-exhaustive match on bool",
			`x: Bool = true; x ? | true -> 1`,
			true, // Missing false case
		},
		{
			"exhaustive match with default",
			`x: Bool = true; x ? | true -> 1 | _ -> 0`,
			false,
		},
		{
			"exhaustive match on ADT with all variants",
			`type Option: type = .Some(i32) | .None; x: Option = .Some(5); x ? | .Some(v) -> v | .None -> 0`,
			false,
		},
		{
			"non-exhaustive match on ADT",
			`type Option: type = .Some(i32) | .None; x: Option = .Some(5); x ? | .Some(v) -> v`,
			true, // Missing .None case
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

// TestMatchExpression_JoinTypes tests that match expressions return the join of branch types
func TestMatchExpression_JoinTypes(t *testing.T) {
	tests := []struct {
		name         string
		input        string
		expectedType string
	}{
		{
			"match with same return types",
			`x: Bool = true; x ? | true -> 1 | false -> 2`,
			"u8", // Both branches return u8
		},
		{
			"match with different return types creates union",
			`x: Bool = true; x ? | true -> 1 | false -> "hello"`,
			"u8 | string", // Union of u8 and string
		},
		{
			"match with never branch",
			`x: Bool = true; x ? | true -> 1 | false -> (fn() -> never { loop() })()`,
			"u8", // never is absorbed in join
		},
		{
			"match with any branch",
			`x: Bool = true; x ? | true -> 1 | false -> (any_value: any)`,
			"any", // any is top, so join is any
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			tc := setupTypeChecker(tt.input)
			program := parseProgram(tt.input)
			tc.CheckProgram(program)

			// Find the match expression and check its type
			var matchExpr *ast.MatchExpression
			for _, stmt := range program.Statements {
				if es, ok := stmt.(*ast.ExpressionStatement); ok {
					if me, ok := es.Expression.(*ast.MatchExpression); ok {
						matchExpr = me
						break
					}
				}
			}

			if matchExpr == nil {
				t.Fatalf("No match expression found in program")
			}

			matchType := tc.CheckExpression(matchExpr)
			if matchType == nil {
				t.Fatalf("Match expression type is nil, errors: %v", tc.Errors())
			}

			if matchType.String() != tt.expectedType {
				t.Errorf("Match expression type = %s, expected %s", matchType, tt.expectedType)
			}
		})
	}
}

// TestMatchExpression_NeverBranches tests that never branches are handled correctly
func TestMatchExpression_NeverBranches(t *testing.T) {
	tests := []struct {
		name     string
		input    string
		hasError bool
	}{
		{
			"match with never branch",
			`x: Bool = true; x ? | true -> 1 | false -> (fn() -> never { loop() })()`,
			false, // never is valid in match
		},
		{
			"match with all never branches",
			`x: Bool = true; x ? | true -> (fn() -> never { loop() })() | false -> (fn() -> never { loop() })()`,
			false, // All never branches -> never return type
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

// TestMatchExpression_TypeNarrowing tests that pattern matching narrows types
func TestMatchExpression_TypeNarrowing(t *testing.T) {
	tests := []struct {
		name     string
		input    string
		hasError bool
	}{
		{
			"narrowing in match arm",
			`type Option: type = .Some(i32) | .None; x: Option = .Some(5); x ? | .Some(v) -> v + 1 | .None -> 0`,
			false, // v should be narrowed to i32 in .Some arm
		},
		{
			"narrowing with field access",
			`type Result: type = .Ok(i32) | .Err(string); x: Result = .Ok(42); x ? | .Ok(v) -> v | .Err(e) -> 0`,
			false, // v should be i32, e should be string
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

// TestMatchExpression_EmptyMatch tests edge cases
func TestMatchExpression_EmptyMatch(t *testing.T) {
	tests := []struct {
		name     string
		input    string
		hasError bool
	}{
		{
			"match with no arms",
			`x: Bool = true; x ?`,
			true, // Empty match should error
		},
		{
			"match on never type",
			`x: never = (fn() -> never { loop() })(); x ? | _ -> 1`,
			false, // Match on never is valid (unreachable code)
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

// TestMatchExpression_WildcardPattern tests wildcard patterns
func TestMatchExpression_WildcardPattern(t *testing.T) {
	tests := []struct {
		name     string
		input    string
		hasError bool
	}{
		{
			"wildcard as last arm",
			`x: Bool = true; x ? | true -> 1 | _ -> 0`,
			false,
		},
		{
			"wildcard as first arm",
			`x: Bool = true; x ? | _ -> 0 | true -> 1`,
			false, // Wildcard should match first
		},
		{
			"multiple wildcards",
			`x: Bool = true; x ? | _ -> 0 | _ -> 1`,
			false, // Multiple wildcards are allowed (second is unreachable)
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
