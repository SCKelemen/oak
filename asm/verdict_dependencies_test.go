package asm

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

func TestVerifyCompositeResultRetainsCalleeDependency(t *testing.T) {
	program := "Pair: type = struct { a: u64, b: u64 }\ninc: (x: u64) -> u64 = x + u64(1)\n"
	p := parser.New(layout.New(scanner.New(program)))
	parsed := p.ParseProgram()
	if errs := p.Errors(); len(errs) != 0 {
		t.Fatal(errs)
	}
	records := map[string]*ast.RecordLiteral{}
	var callee *ast.FunctionStatement
	for _, statement := range parsed.Statements {
		switch declaration := statement.(type) {
		case *ast.ADTType:
			records[declaration.Name.Value] = declaration.Variants[0].Literal.(*ast.RecordLiteral)
		case *ast.FunctionStatement:
			callee = declaration
		}
	}
	composites := map[string]Composite{"Pair": {
		Size: 16,
		Fields: []CompositeField{
			{Name: "a", Offset: 0, Size: 8, Scalar: "u64"},
			{Name: "b", Offset: 8, Size: 8, Scalar: "u64"},
		},
	}}
	decl := "make_pair: (x: u64) -> Pair"
	unit, errs := ParseUnit("composite_call.oakasm", decl+` = {
  bind x0 = x
  clobber x29, x30
  frame 16
  sub sp, sp, #16
  stp x29, x30, [sp]
  bl inc
  mov x1, x0
  add x1, x1, #1
  ldp x29, x30, [sp]
  add sp, sp, #16
  ret
}
`)
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	fn := unit.Functions[0]
	fn.Callees = map[string]*ast.FunctionStatement{"inc": callee}
	fn.Composites = composites
	fn.Records = records
	sig, err := parseSignature(decl)
	if err != nil {
		t.Fatal(err)
	}
	if findings := Check(fn, sig, map[string]bool{"inc": true}); len(findings) != 0 {
		t.Fatalf("checker: %v", findings)
	}
	spec, err := parseSignatureWithBody(decl + " = Pair { a: inc(x), b: inc(x) + u64(1) }")
	if err != nil {
		t.Fatal(err)
	}
	verdict := Verify(fn, sig, spec.Body)
	if verdict.Kind != VerdictProven || !strings.Contains(verdict.Message, "both result chunks") ||
		strings.Join(verdict.Callees, ",") != "inc" {
		t.Fatalf("a proven composite caller must retain its callee dependency, got %s: %s, callees %v", verdict.Kind, verdict.Message, verdict.Callees)
	}
}

func TestVerdictWithCalleesProducesStableDefensiveUnion(t *testing.T) {
	first := []string{"left", "shared"}
	second := []string{"shared", "right"}
	verdict := verdictWithCallees(Verdict{Kind: VerdictProven}, first, second)
	if got := strings.Join(verdict.Callees, ","); got != "left,shared,right" {
		t.Fatalf("callee union = %q", got)
	}
	first[0] = "mutated"
	if verdict.Callees[0] != "left" {
		t.Fatalf("callee union aliases executor storage: %v", verdict.Callees)
	}
}
