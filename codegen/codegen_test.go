package codegen

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/typechecker"
)

func TestCodeGenerator_SimpleFunction(t *testing.T) {
	input := `
package main

fn add( a: i32, b: i32 ) -> i32
  a + b
`

	l := scanner.New(input)
	p := parser.New(l)
	program := p.ParseProgram()

	if len(p.Errors()) > 0 {
		t.Fatalf("Parser errors: %v", p.Errors())
	}

	env := object.NewEnvironment()
	tc := typechecker.New(env)
	tc.CheckProgram(program)

	cg := New("main", tc)
	output, err := cg.Generate(program, tc)
	if err != nil {
		t.Fatalf("Code generation error: %v", err)
	}

	if output == "" {
		t.Fatal("Generated code is empty")
	}

	// Check for expected C constructs
	if !contains(output, "i32 oak_add") {
		t.Errorf("Expected function signature not found in output")
	}
}

func TestCodeGenerator_ADT(t *testing.T) {
	input := `
package main

Status: type
  = Ok
  | NotFound
`

	l := scanner.New(input)
	p := parser.New(l)
	program := p.ParseProgram()

	if len(p.Errors()) > 0 {
		t.Fatalf("Parser errors: %v", p.Errors())
	}

	env := object.NewEnvironment()
	tc := typechecker.New(env)
	tc.CheckProgram(program)

	cg := New("main", tc)
	output, err := cg.Generate(program, tc)
	if err != nil {
		t.Fatalf("Code generation error: %v", err)
	}

	// Check for ADT enum and struct
	if !contains(output, "oak_Status_tag") {
		t.Errorf("Expected ADT tag enum not found")
	}
	if !contains(output, "typedef struct oak_Status") {
		t.Errorf("Expected ADT struct not found")
	}
}

func contains(s, substr string) bool {
	return strings.Contains(s, substr)
}

