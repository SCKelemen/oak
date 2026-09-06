package codegen

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/typechecker"
)

func generateC(t *testing.T, input string) string {
	t.Helper()
	l := scanner.New(input)
	p := parser.New(l)
	program := p.ParseProgram()
	if len(p.Errors()) > 0 {
		t.Fatalf("parser errors: %v", p.Errors())
	}
	env := object.NewEnvironment()
	tc := typechecker.New(env)
	tc.CheckProgram(program)
	cg := New("main", tc)
	output, err := cg.Generate(program, tc)
	if err != nil {
		t.Fatalf("code generation error: %v", err)
	}
	return output
}

// Self tail recursion compiles to a loop (docs/spec/85-discipline.md): the
// frame is reused, so stack depth stays constant regardless of iteration
// count.
func TestSelfTailRecursionCompilesToLoop(t *testing.T) {
	output := generateC(t, `
package main

fn countdown( n: i32, acc: i32 ) -> i32 {
  countdown(n - 1, acc + n)
}
`)
	if !strings.Contains(output, "while (1)") {
		t.Fatalf("loop-lowered function must emit a loop, got:\n%s", output)
	}
	if !strings.Contains(output, "continue;") {
		t.Fatalf("tail self-call must continue the loop, got:\n%s", output)
	}
	if strings.Contains(output, "return oak_countdown") {
		t.Fatalf("tail self-call must not be emitted as a recursive call, got:\n%s", output)
	}
	if !strings.Contains(output, "__oak_tail_0") || !strings.Contains(output, "__oak_tail_1") {
		t.Fatalf("parameter rebinding must go through temporaries, got:\n%s", output)
	}
}

// Non-recursive functions keep the plain return shape.
func TestNonRecursiveFunctionKeepsPlainReturn(t *testing.T) {
	output := generateC(t, `
package main

fn add( a: i32, b: i32 ) -> i32
  a + b
`)
	if strings.Contains(output, "while (1)") {
		t.Fatalf("non-recursive function must not be loop-wrapped, got:\n%s", output)
	}
}
