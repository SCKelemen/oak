package nativegen

import (
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/typechecker"
)

func TestCompileTrimCalleeSavesCandidate(t *testing.T) {
	parser := parser.New(layout.New(scanner.New(`get: (s: [*]u64, i: u32): u64 { s[i] }`)))
	program := parser.ParseProgram()
	if errors := parser.Errors(); len(errors) != 0 {
		t.Fatal(errors)
	}
	checker := typechecker.New(object.NewEnvironment())
	checker.CheckProgram(program)
	if errors := checker.Errors(); len(errors) != 0 {
		t.Fatal(errors)
	}
	function := program.Statements[0].(*ast.FunctionStatement)
	functions := map[string]*ast.FunctionStatement{"get": function}
	base := Lane{Arch: asm.ArchArm64, NoReductions: true, Reallocate: true}
	before, err := CompileFor(base, function, functions, nil, nil, nil, checker)
	if err != nil {
		t.Fatal(err)
	}
	afterLane := base
	afterLane.TrimCalleeSaves = true
	after, err := CompileFor(afterLane, function, functions, nil, nil, nil, checker)
	if err != nil {
		t.Fatal(err)
	}
	if sites := TrimmedCalleeSaves(after); sites == 0 {
		t.Fatal("callee-save candidate found no dead home")
	}
	beforeMetrics, afterMetrics := Metrics(before), Metrics(after)
	if afterMetrics.Instructions >= beforeMetrics.Instructions || afterMetrics.Loads >= beforeMetrics.Loads || afterMetrics.Stores >= beforeMetrics.Stores {
		t.Fatalf("callee-save candidate did not reduce code and frame traffic: before=%+v after=%+v", beforeMetrics, afterMetrics)
	}
	if findings := asm.Check(after, function, map[string]bool{"get": true}); len(findings) != 0 {
		t.Fatalf("trimmed candidate failed the seam check: %v", findings)
	}
	if verdict := asm.Verify(after, function, function.Body); verdict.Kind != asm.VerdictProven {
		t.Fatalf("trimmed candidate did not prove: %s", verdict.Message)
	}
}
