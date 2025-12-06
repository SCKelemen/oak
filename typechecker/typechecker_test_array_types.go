package typechecker

import (
	"testing"
)

func TestTypeChecker_ArrayType_Slice(t *testing.T) {
	tests := []struct {
		input    string
		hasError bool
	}{
		{"arr: []i32 = [1, 2, 3]", false},
		{"arr: []string", false},
		{"arr: []i32 = [1, 2, 3]; arr[0]", false},
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

func TestTypeChecker_ArrayType_FixedSize(t *testing.T) {
	tests := []struct {
		name     string
		input    string
		hasError bool
	}{
		{
			name:     "fixed-size array declaration",
			input:    "arr: [10]i32",
			hasError: false,
		},
		{
			name:     "fixed-size array in function parameter",
			input:    "fn process(buf: [10]i32) -> () { }",
			hasError: false,
		},
		{
			name:     "fixed-size array indexing",
			input:    "arr: [10]i32; arr[0]",
			hasError: false,
		},
		{
			name:     "different sized arrays are different types",
			input:    "arr1: [10]i32; arr2: [20]i32; arr1 = arr2",
			hasError: true, // Type mismatch
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			tc := setupTypeChecker(tt.input)
			program := parseProgram(tt.input)
			tc.CheckProgram(program)

			hasError := len(tc.Errors()) > 0
			if hasError != tt.hasError {
				t.Errorf("expected error=%v, got errors=%v", tt.hasError, tc.Errors())
			}
		})
	}
}

func TestTypeChecker_ArrayType_SliceVsFixed(t *testing.T) {
	tests := []struct {
		name     string
		input    string
		hasError bool
	}{
		{
			name:     "slice and fixed-size array are different types",
			input:    "arr1: []i32; arr2: [10]i32; arr1 = arr2",
			hasError: true, // Type mismatch
		},
		{
			name:     "both slices can be assigned",
			input:    "arr1: []i32 = [1, 2]; arr2: []i32 = [3, 4]; arr1 = arr2",
			hasError: false,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			tc := setupTypeChecker(tt.input)
			program := parseProgram(tt.input)
			tc.CheckProgram(program)

			hasError := len(tc.Errors()) > 0
			if hasError != tt.hasError {
				t.Errorf("expected error=%v, got errors=%v", tt.hasError, tc.Errors())
			}
		})
	}
}



