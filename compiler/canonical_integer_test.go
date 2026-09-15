package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/opt"
)

func TestPostSpecializationIntegerCanonicalization(t *testing.T) {
	source := `
canonicalInt[T]: (x: u32, witness: T): u32 {
  a: u32 = x + u32(0)
  b: u32 = u32(0) + a
  c: u32 = b - u32(0)
  d: u32 = c * u32(1)
  e: u32 = u32(1) * d
  f: u32 = e / u32(1)
  g: u32 = f | u32(0)
  h: u32 = u32(0) | g
  i: u32 = h ^ u32(0)
  j: u32 = u32(0) ^ i
  k: u32 = j << u32(0)
  k >> u32(0)
}
main: (): i32 {
  canonicalInt(u32(42), u8(0)) == u32(42) ? 42 | 1
}
`
	comp := New().WithSource("canonical_integer.oak", source)
	comp.options.InlineHelpers = true
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}

	var specialized *ast.FunctionStatement
	for _, statement := range model.Tree.Root.Statements {
		function, ok := statement.(*ast.FunctionStatement)
		if ok && function.Name != nil && strings.HasPrefix(function.Name.Value, "canonicalInt_") {
			specialized = function
			break
		}
	}
	if specialized == nil {
		t.Fatal("canonicalInt[T] was not monomorphized before canonicalization")
	}
	body := specialized.Body.String()
	for _, operator := range []string{" + ", " - ", " * ", " / ", " | ", " ^ ", " << ", " >> "} {
		if strings.Contains(body, operator) {
			t.Fatalf("specialized body retained %q: %s", operator, body)
		}
	}
	found := false
	for _, remark := range model.Optimizations.Remarks {
		if remark.Transform != OptimizationCanonicalInteger || remark.Function != specialized.Name.Value {
			continue
		}
		found = true
		if remark.Kind != opt.Passed || !strings.Contains(remark.Message, "canonicalized 12 fixed-width integer expression(s)") || !strings.Contains(remark.Message, "post-specialization program re-typechecked") || len(remark.Facts) != 2 {
			t.Fatalf("integer canonicalization remark = %+v", remark)
		}
	}
	if !found {
		t.Fatalf("no integer canonicalization remark for %s: %+v", specialized.Name.Value, model.Optimizations.Remarks)
	}
	if code, abnormal := buildAndRun(t, "canonical_integer", source); abnormal || code != 42 {
		t.Fatalf("canonicalized C result = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

func TestIntegerCanonicalizationExcludesFloatsAndOperandDeletingRules(t *testing.T) {
	source := `
floatKeep: (x: f32): f32 = x + 0.0
widenKeep: (x: u8): u16 = x + u16(0)
integerKeep: (x: u32): u32 {
  y: u32 = x * u32(0)
  y % u32(1)
}
main: (): i32 = 0
`
	comp := New().WithSource("canonical_exclusions.oak", source)
	comp.options.InlineHelpers = true
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	seenFloat, seenWiden, seenInteger := false, false, false
	for _, statement := range model.Tree.Root.Statements {
		function, ok := statement.(*ast.FunctionStatement)
		if !ok || function.Name == nil {
			continue
		}
		switch function.Name.Value {
		case "floatKeep":
			seenFloat = true
			if got := function.Body.String(); !strings.Contains(got, " + ") {
				t.Fatalf("float identity was rewritten: %s", got)
			}
		case "widenKeep":
			seenWiden = true
			if got := function.Body.String(); !strings.Contains(got, " + ") {
				t.Fatalf("widening identity was rewritten: %s", got)
			}
		case "integerKeep":
			seenInteger = true
			got := function.Body.String()
			if !strings.Contains(got, " * ") || !strings.Contains(got, " % ") {
				t.Fatalf("operand-deleting identity was rewritten: %s", got)
			}
		}
	}
	if !seenFloat || !seenWiden || !seenInteger {
		t.Fatalf("exclusion functions missing: float=%v widen=%v integer=%v", seenFloat, seenWiden, seenInteger)
	}
	for _, remark := range model.Optimizations.Remarks {
		if remark.Transform == OptimizationCanonicalInteger && (remark.Function == "floatKeep" || remark.Function == "widenKeep" || remark.Function == "integerKeep") {
			t.Fatalf("excluded expression reported as canonicalized: %+v", remark)
		}
	}
}
