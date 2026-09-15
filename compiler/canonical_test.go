package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/opt"
	"github.com/SCKelemen/oak/typechecker"
)

func TestPostSpecializationBooleanCanonicalization(t *testing.T) {
	source := `
canonical[T]: (x: Bool, witness: T): Bool {
  a: Bool = true
  b: Bool = true && x
  c: Bool = false || a
  d: Bool = b && true
  e: Bool = c || false
  !!(d == true)
}
main: (): i32 {
  canonical(true, u32(0)) ? 42 | 1
}
`
	comp := New().WithSource("canonical.oak", source)
	comp.options.InlineHelpers = true
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}

	var specialized *ast.FunctionStatement
	for _, statement := range model.Tree.Root.Statements {
		function, ok := statement.(*ast.FunctionStatement)
		if ok && function.Name != nil && strings.HasPrefix(function.Name.Value, "canonical_") {
			specialized = function
			break
		}
	}
	if specialized == nil {
		t.Fatal("canonical[T] was not monomorphized before canonicalization")
	}
	body := specialized.Body.String()
	if strings.Contains(body, "&&") || strings.Contains(body, "||") || strings.Contains(body, "!") || strings.Contains(body, "==") {
		t.Fatalf("specialized body was not canonicalized: %s", body)
	}

	found := false
	for _, remark := range model.Optimizations.Remarks {
		if remark.Transform != OptimizationCanonicalBool || remark.Function != specialized.Name.Value {
			continue
		}
		found = true
		if remark.Kind != opt.Passed || !strings.Contains(remark.Message, "canonicalized 6 boolean expression(s)") || !strings.Contains(remark.Message, "post-specialization program re-typechecked") || len(remark.Facts) != 2 {
			t.Fatalf("canonicalization remark = %+v", remark)
		}
	}
	if !found {
		t.Fatalf("no canonicalization remark for %s: %+v", specialized.Name.Value, model.Optimizations.Remarks)
	}
}

func TestBooleanCanonicalizationDoesNotMutateLiteralTokenIdentity(t *testing.T) {
	source := `
keep: (): Bool = !false
main: (): i32 = 0
`
	comp := New().WithSource("canonical_literal_identity.oak", source)
	comp.options.InlineHelpers = true
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	found := false
	for _, statement := range model.Tree.Root.Statements {
		function, ok := statement.(*ast.FunctionStatement)
		if !ok || function.Name == nil || function.Name.Value != "keep" {
			continue
		}
		found = true
		if got := function.Body.String(); !strings.Contains(got, "!false") {
			t.Fatalf("literal token identity was mutated: %s", got)
		}
	}
	if !found {
		t.Fatal("keep function not found")
	}
	for _, remark := range model.Optimizations.Remarks {
		if remark.Transform == OptimizationCanonicalBool && remark.Function == "keep" {
			t.Fatalf("literal negation was reported as canonicalized: %+v", remark)
		}
	}
}

func TestBooleanCanonicalizationRetainsNonliteralShortCircuitOperands(t *testing.T) {
	source := `
pub touch: (): Bool = true
keep: (): Bool = false && touch()
main: (): i32 = 0
`
	comp := New().WithSource("short_circuit.oak", source)
	comp.options.InlineHelpers = true
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, statement := range model.Tree.Root.Statements {
		function, ok := statement.(*ast.FunctionStatement)
		if !ok || function.Name == nil || function.Name.Value != "keep" {
			continue
		}
		if got := function.Body.String(); !strings.Contains(got, "false && touch()") {
			t.Fatalf("non-literal operand was erased from short circuit: %s", got)
		}
		return
	}
	t.Fatal("keep function not found")
}

func TestBooleanCanonicalizationDoesNotMaskTypeErrors(t *testing.T) {
	_, err := New().WithSource("invalid.oak", `main: (): Bool = true && u32(1)`).Optimizations().Get()
	if err == nil || !strings.Contains(err.Error(), "Bool") {
		t.Fatalf("invalid pre-optimization expression was accepted: %v", err)
	}
}

func TestBooleanCanonicalizationRetainsGenericResourceContracts(t *testing.T) {
	consuming := typechecker.ResourceTransitionDeclaration{
		Name: "tag", Callable: "tag", From: "Open", To: "Closed",
		Parameters: []typechecker.ResourceParameterDeclaration{{Index: 0, Mode: typechecker.ResourceParameterConsumed}},
	}
	program := boundaryBase + `
tag[T]: (h: Handle, label: T): () {
  flag: Bool = !!true
}
f: (h: Handle): u32 {
  tag(h, u32(1))
  0
}
main: (): i32 = 0
`
	comp := New().WithSource("canonical_resource.oak", program).WithResourceProtocols(boundaryDeclarations(consuming))
	comp.options.InlineHelpers = true
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	found := false
	for _, remark := range model.Optimizations.Remarks {
		found = found || remark.Transform == OptimizationCanonicalBool && strings.HasPrefix(remark.Function, "tag_")
	}
	if !found {
		t.Fatalf("generic resource specialization was not canonicalized: %+v", model.Optimizations.Remarks)
	}

	invalid := strings.Replace(program, "  0\n}\nmain", "  h.id\n}\nmain", 1)
	bad := New().WithSource("canonical_resource_invalid.oak", invalid).WithResourceProtocols(boundaryDeclarations(consuming))
	bad.options.InlineHelpers = true
	_, err = bad.Check().Get()
	expectCode(t, "canonical-resource-specialization", err, typechecker.CodeResourceUsedAfterConsume)
}

func TestPostSpecializationValidationReplaysGenericADTInstantiations(t *testing.T) {
	source := `
Pair[A, B]: type = struct { left: A, right: B }
read: (p: Pair[u32, u8], x: u32): u32 = x + u32(0)
main: (): i32 {
  p: Pair[u32, u8] = Pair { left: u32(42), right: u8(1) }
  i32_bits_u32(read(p, p.left))
}
`
	comp := New().WithSource("canonical_generic_adt.oak", source)
	comp.options.InlineHelpers = true
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	canonicalized := false
	for _, remark := range model.Optimizations.Remarks {
		canonicalized = canonicalized || remark.Transform == OptimizationCanonicalInteger && remark.Function == "read"
	}
	if !canonicalized {
		t.Fatalf("generic ADT program did not reach post-specialization validation: %+v", model.Optimizations.Remarks)
	}
	for _, statement := range model.Tree.Root.Statements {
		declaration, isADT := statement.(*ast.ADTType)
		if isADT && declaration.Name != nil && declaration.Name.Value == "Pair_u32_u8" {
			t.Fatal("validation-only generic ADT declaration leaked into the emitted AST")
		}
	}
}
