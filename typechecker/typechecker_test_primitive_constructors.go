package typechecker

import (
	"testing"
)

func TestTypeChecker_PrimitiveConstructor_Widening(t *testing.T) {
	tests := []struct {
		name     string
		input    string
		hasError bool
	}{
		{
			name:     "u8 to u32 widening",
			input:    "x: u8 = 5; y: u32 = u32(x)",
			hasError: false,
		},
		{
			name:     "u16 to u64 widening",
			input:    "x: u16 = 100; y: u64 = u64(x)",
			hasError: false,
		},
		{
			name:     "i8 to i32 widening",
			input:    "x: i8 = -5; y: i32 = i32(x)",
			hasError: false,
		},
		{
			name:     "literal in constructor",
			input:    "x: u32 = u32(42)",
			hasError: false,
		},
		{
			name:     "invalid widening (signed to unsigned)",
			input:    "x: i32 = 5; y: u32 = u32(x)",
			hasError: true,
		},
		{
			name:     "invalid widening (narrowing)",
			input:    "x: u32 = 5; y: u8 = u8(x)",
			hasError: true, // Should use narrowing function
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

func TestTypeChecker_NarrowingFunction_Trunc(t *testing.T) {
	tests := []struct {
		name     string
		input    string
		hasError bool
	}{
		{
			name:     "u32 to u8 truncation",
			input:    "x: u32 = 1000; y: u8 = u8_trunc_u32(x)",
			hasError: false,
		},
		{
			name:     "u64 to u16 truncation",
			input:    "x: u64 = 50000; y: u16 = u16_trunc_u64(x)",
			hasError: false,
		},
		{
			name:     "invalid truncation (wrong source type)",
			input:    "x: u16 = 100; y: u8 = u8_trunc_u32(x)",
			hasError: true,
		},
		{
			name:     "invalid truncation (wrong target type)",
			input:    "x: u32 = 100; y: u8 = u16_trunc_u32(x)",
			hasError: true,
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

func TestTypeChecker_NarrowingFunction_Saturating(t *testing.T) {
	tests := []struct {
		name     string
		input    string
		hasError bool
	}{
		{
			name:     "u32 to u8 saturating",
			input:    "x: u32 = 1000; y: u8 = u8_saturating_u32(x)",
			hasError: false,
		},
		{
			name:     "u64 to u16 saturating",
			input:    "x: u64 = 100000; y: u16 = u16_saturating_u64(x)",
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

func TestTypeChecker_NarrowingFunction_Checked(t *testing.T) {
	tests := []struct {
		name     string
		input    string
		hasError bool
	}{
		{
			name:     "u32 to u8 checked returns Result",
			input:    "x: u32 = 100; res := u8_checked_u32(x)",
			hasError: false,
		},
		{
			name:     "u64 to u16 checked",
			input:    "x: u64 = 50000; res := u16_checked_u64(x)",
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

func TestTypeChecker_CastableConstructor(t *testing.T) {
	tests := []struct {
		name     string
		input    string
		hasError bool
	}{
		{
			name:     "string identity conversion",
			input:    "s: string = \"hello\"; s2: string = string(s)",
			hasError: false,
		},
		{
			name:     "byte alias",
			input:    "b: u8 = 42; b2: u8 = byte(b)",
			hasError: false,
		},
		{
			name:     "invalid castable (wrong type)",
			input:    "x: i32 = 42; s: string = string(x)",
			hasError: true,
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

func TestTypeChecker_LiteralRangeChecking(t *testing.T) {
	tests := []struct {
		name     string
		input    string
		hasError bool
	}{
		{
			name:     "literal fits in u8",
			input:    "x: u8 = 255",
			hasError: false,
		},
		{
			name:     "literal too large for u8",
			input:    "x: u8 = 256",
			hasError: true,
		},
		{
			name:     "literal fits in u32",
			input:    "x: u32 = 4294967295",
			hasError: false,
		},
		{
			name:     "literal in constructor",
			input:    "x: u8 = u8(255)",
			hasError: false,
		},
		{
			name:     "literal too large in constructor",
			input:    "x: u8 = u8(256)",
			hasError: true,
		},
		{
			name:     "negative literal for signed type",
			input:    "x: i8 = -128",
			hasError: false,
		},
		{
			name:     "negative literal too small",
			input:    "x: i8 = -129",
			hasError: true,
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



