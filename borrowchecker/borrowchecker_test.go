package borrowchecker

import (
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/typechecker"
)

func setupBorrowChecker(t *testing.T, input string) (*BorrowChecker, *ast.Program, *typechecker.TypeChecker) {
	bc, program, tc := setupBorrowCheckerForTest(input)
	if program == nil && len(parser.New(scanner.New(input)).Errors()) > 0 {
		// Print errors for debugging
		for _, err := range parser.New(scanner.New(input)).Errors() {
			t.Logf("Parser error: %s", err)
		}
	}
	return bc, program, tc
}

func TestBorrowChecker_ViewCreation(t *testing.T) {
	tests := []struct {
		name     string
		input    string
		hasError bool
	}{
		{
			"create view from free array via slice",
			"buf: [16]u8\nv: []u8 = buf[0:16]",
			false,
		},
		{
			"multiple views from same array via slices",
			"buf: [16]u8\nv1: []u8 = buf[0:8]\nv2: []u8 = buf[8:16]",
			false,
		},
		// Note: view() and span() are conceptual primitives from the spec
		// They will be implemented as methods or desugaring targets
		// For now, we test with slice syntax which is the primary user-facing feature
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			bc, program, tc := setupBorrowChecker(t, tt.input)
			if program == nil {
				t.Fatalf("Failed to parse program")
			}

			bc.CheckProgram(program, tc.Env())

			hasError := len(bc.Errors()) > 0
			if hasError != tt.hasError {
				t.Errorf("Expected error=%v, got errors=%v", tt.hasError, bc.Errors())
			}
		})
	}
}

func TestBorrowChecker_SpanCreation(t *testing.T) {
	tests := []struct {
		name     string
		input    string
		hasError bool
	}{
		{
			"create span from free array",
			"buf: [16]u8\ns: [*]u8 = span(&buf)",
			false,
		},
		// Note: span() is a conceptual primitive from the spec
		// Slicing owned arrays produces views (read-only) by default
		// To get a writable span, users would need to call span() method
		// For now, we test basic functionality
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			bc, program, tc := setupBorrowChecker(t, tt.input)
			if program == nil {
				t.Fatalf("Failed to parse program")
			}

			bc.CheckProgram(program, tc.Env())

			hasError := len(bc.Errors()) > 0
			if hasError != tt.hasError {
				t.Errorf("Expected error=%v, got errors=%v", tt.hasError, bc.Errors())
			}
		})
	}
}

func TestBorrowChecker_LexicalScoping(t *testing.T) {
	tests := []struct {
		name     string
		input    string
		hasError bool
	}{
		// Note: Block statement syntax with variable declarations needs to be tested
		// when we have proper block parsing support. For now, we test sequential declarations.
		{
			"sequential views from same array",
			"buf: [16]u8\nv1: []u8 = buf[0:8]\nv2: []u8 = buf[8:16]",
			false, // Multiple views from same array are allowed
		},
		// Note: v1 restriction on borrows escaping blocks will be enforced
		// when we implement proper scope tracking
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			bc, program, tc := setupBorrowChecker(t, tt.input)
			if program == nil {
				t.Fatalf("Failed to parse program")
			}

			bc.CheckProgram(program, tc.Env())

			hasError := len(bc.Errors()) > 0
			if hasError != tt.hasError {
				t.Errorf("Expected error=%v, got errors=%v", tt.hasError, bc.Errors())
			}
		})
	}
}

func TestBorrowChecker_SliceOperations(t *testing.T) {
	tests := []struct {
		name     string
		input    string
		hasError bool
	}{
		{
			"slice owned array creates view",
			"buf: [16]u8\nv: []u8 = buf[0:8]",
			false,
		},
		{
			"slice view creates subslice",
			"buf: [16]u8\nv1: []u8 = buf[0:16]\nv2: []u8 = v1[4:8]",
			false,
		},
		{
			"multiple slices from same array",
			"buf: [16]u8\nv1: []u8 = buf[0:8]\nv2: []u8 = buf[8:16]",
			false,
		},
		{
			"slice with negative index",
			"buf: [16]u8\nv: []u8 = buf[0:-1]",
			false, // Negative indices are normalized during evaluation
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			bc, program, tc := setupBorrowChecker(t, tt.input)
			if program == nil {
				t.Fatalf("Failed to parse program")
			}

			bc.CheckProgram(program, tc.Env())

			hasError := len(bc.Errors()) > 0
			if hasError != tt.hasError {
				t.Errorf("Expected error=%v, got errors=%v", tt.hasError, bc.Errors())
			}
		})
	}
}
