package compiler

import (
	"errors"
	"testing"

	"github.com/SCKelemen/oak/typechecker"
)

// Contracts across callable boundaries (docs/spec/50-borrowing.md section
// 9, authority roadmap milestone 2): a function value initialized from a
// global function carries that function's resource contract, so calling
// through it consumes or borrows exactly as the direct call would; a
// function value of unknown provenance has an unknown contract, and a
// resource passed through it fails closed (OAK-B0115); a contract declared
// for a generic template holds for every specialization.
func boundaryDeclarations(extra ...typechecker.ResourceTransitionDeclaration) []typechecker.ResourceProtocolDeclaration {
	mode := func(m typechecker.ResourceParameterMode) []typechecker.ResourceParameterDeclaration {
		return []typechecker.ResourceParameterDeclaration{{Index: 0, Mode: m}}
	}
	transitions := []typechecker.ResourceTransitionDeclaration{
		{Name: "inspect", Callable: "inspect", From: "Open", To: "Open", Parameters: mode(typechecker.ResourceParameterBorrowed)},
		{Name: "close", Callable: "close", From: "Open", To: "Closed", Parameters: mode(typechecker.ResourceParameterConsumed)},
	}
	transitions = append(transitions, extra...)
	return []typechecker.ResourceProtocolDeclaration{{
		Name:          "HandleLifecycle",
		ResourceTypes: []string{"Handle"},
		States:        []string{"Open", "Closed"},
		Initial:       "Open",
		Transitions:   transitions,
	}}
}

const boundaryBase = `
Handle: type = struct { id: u32 }
inspect: (h: Handle): () = {}
close: (h: Handle): () = {}
plain: (h: Handle): () = {}
`

func checkBoundaries(t *testing.T, name, body string, extra ...typechecker.ResourceTransitionDeclaration) error {
	t.Helper()
	_, err := New().
		WithSource(name+".oak", boundaryBase+body).
		WithResourceProtocols(boundaryDeclarations(extra...)).
		Check().
		Get()
	return err
}

func expectCode(t *testing.T, name string, err error, code string) {
	t.Helper()
	if err == nil {
		t.Fatalf("%s: expected %s, program accepted", name, code)
	}
	var diagnosticErr *DiagnosticError
	if !errors.As(err, &diagnosticErr) {
		t.Fatalf("%s: expected DiagnosticError, got %T: %v", name, err, err)
	}
	for _, d := range diagnosticErr.Diagnostics {
		if d != nil && d.Code == code {
			return
		}
	}
	t.Fatalf("%s: expected %s, got %#v", name, code, diagnosticErr.Diagnostics)
}

func TestFunctionValueCarriesConsumingContract(t *testing.T) {
	// Consuming through a function value invalidates the caller's alias.
	err := checkBoundaries(t, "indirect-consume", `
f: (h: Handle): u32 {
  shutdown: (Handle) -> () = close
  shutdown(h)
  h.id
}
`)
	expectCode(t, "indirect-consume", err, typechecker.CodeResourceUsedAfterConsume)
}

func TestFunctionValueCarriesBorrowedContract(t *testing.T) {
	// Borrowing through a function value leaves the resource live.
	if err := checkBoundaries(t, "indirect-borrow", `
f: (h: Handle): u32 {
  look: (Handle) -> () = inspect
  look(h)
  look(h)
  h.id
}
`); err != nil {
		t.Fatalf("borrowed call through a function value should keep authority: %v", err)
	}
}

func TestFunctionValueFromUnmarkedFunctionKeepsOrdinaryMeaning(t *testing.T) {
	if err := checkBoundaries(t, "unmarked-value", `
f: (h: Handle): u32 {
  touch: (Handle) -> () = plain
  touch(h)
  h.id
}
`); err != nil {
		t.Fatalf("an unmarked function's value has an empty, known contract: %v", err)
	}
}

func TestUnknownCallableContractFailsClosed(t *testing.T) {
	// A function-typed parameter has no checked contract.
	expectCode(t, "parameter", checkBoundaries(t, "parameter", `
apply: (op: (Handle) -> (), h: Handle): u32 {
  op(h)
  h.id
}
`), typechecker.CodeResourceUnknownCallable)
	// A closure literal has none either; today's literals take only
	// integer-typed parameters, so that case cannot yet be written with a
	// resource argument and is covered by the reassignment case below.
	// A reassigned function value has no single contract.
	expectCode(t, "reassigned", checkBoundaries(t, "reassigned", `
f: (h: Handle): u32 {
  op: (Handle) -> () = inspect
  op = close
  op(h)
  h.id
}
`), typechecker.CodeResourceUnknownCallable)
}

// A contract declared for a generic template holds for every
// specialization: consuming through tag[u32] and tag[Bool] both invalidate
// the caller's handle, and the template's own body is checked under the
// template's contract.
func TestSpecializationsRetainTemplateModes(t *testing.T) {
	consuming := typechecker.ResourceTransitionDeclaration{
		Name: "tag", Callable: "tag", From: "Open", To: "Closed",
		Parameters: []typechecker.ResourceParameterDeclaration{{Index: 0, Mode: typechecker.ResourceParameterConsumed}},
	}
	expectCode(t, "specialized-u32", checkBoundaries(t, "specialized-u32", `
tag[T]: (h: Handle, label: T): () = {}
f: (h: Handle): u32 {
  tag(h, u32(1))
  h.id
}
`, consuming), typechecker.CodeResourceUsedAfterConsume)
	expectCode(t, "specialized-bool", checkBoundaries(t, "specialized-bool", `
tag[T]: (h: Handle, label: T): () = {}
g: (h: Handle): u32 {
  tag(h, true)
  h.id
}
`, consuming), typechecker.CodeResourceUsedAfterConsume)
	// A borrowed template forwarding its parameter to a consuming operation
	// is rejected inside the specialized body under the template's contract.
	borrowed := typechecker.ResourceTransitionDeclaration{
		Name: "peek_tagged", Callable: "peek_tagged", From: "Open", To: "Open",
		Parameters: []typechecker.ResourceParameterDeclaration{{Index: 0, Mode: typechecker.ResourceParameterBorrowed}},
	}
	expectCode(t, "specialized-body", checkBoundaries(t, "specialized-body", `
peek_tagged[T]: (h: Handle, label: T): u32 {
  close(h)
  h.id
}
f: (h: Handle): u32 = peek_tagged(h, u32(1))
`, borrowed), typechecker.CodeResourceParameterForwarded)
}
