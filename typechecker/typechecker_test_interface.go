package typechecker

import (
	"testing"
)

func TestTypeChecker_InterfaceType(t *testing.T) {
	tests := []struct {
		input    string
		hasError bool
	}{
		{
			"Reader: interface = fn (self) read(buf: [*]Byte) -> Result[u32, Error]",
			false,
		},
		{
			"Writer: interface = fn (self) write(data: []Byte) -> Result[u32, Error]",
			false,
		},
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

func TestTypeChecker_InterfaceSatisfaction(t *testing.T) {
	tests := []struct {
		name     string
		input    string
		hasError bool
	}{
		{
			name: "type implements interface with matching method",
			input: `
Reader: interface = fn (self) read() -> i32
Uart: type = { port: u32 }
fn (u: *Uart) read() -> i32 { 0 }
`,
			hasError: false,
		},
		{
			name: "type missing required method",
			input: `
Reader: interface = fn (self) read() -> i32
Uart: type = { port: u32 }
`,
			hasError: true, // Uart doesn't implement read method
		},
		{
			name: "method with wrong return type",
			input: `
Reader: interface = fn (self) read() -> i32
Uart: type = { port: u32 }
fn (u: *Uart) read() -> u32 { 0 }
`,
			hasError: true, // Return type mismatch
		},
		{
			name: "method with wrong parameter count",
			input: `
Reader: interface = fn (self) read() -> i32
Uart: type = { port: u32 }
fn (u: *Uart) read(extra: i32) -> i32 { 0 }
`,
			hasError: true, // Parameter count mismatch
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

func TestTypeChecker_InterfaceMethodParameters(t *testing.T) {
	input := `
Reader: interface = fn (self) read(buf: i32, len: u32) -> i32
Uart: type = { port: u32 }
fn (u: *Uart) read(buf: i32, len: u32) -> i32 { 0 }
`

	tc := setupTypeChecker(input)
	program := parseProgram(input)
	tc.CheckProgram(program)

	if len(tc.Errors()) > 0 {
		t.Errorf("unexpected errors: %v", tc.Errors())
	}
}

func TestTypeChecker_InterfaceType_Simple(t *testing.T) {
	// Simple test that should definitely work
	tc := setupTypeChecker("x: i32 = 5")
	program := parseProgram("x: i32 = 5")
	tc.CheckProgram(program)
	if len(tc.Errors()) > 0 {
		t.Errorf("unexpected errors: %v", tc.Errors())
	}
}
