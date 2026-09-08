package compiler

import (
	"errors"
	"testing"

	"github.com/SCKelemen/oak/semir"
	"github.com/SCKelemen/oak/typechecker"
)

func compilerParameterModeDeclarations() []typechecker.ResourceProtocolDeclaration {
	return []typechecker.ResourceProtocolDeclaration{{
		Name:          "HandleLifecycle",
		ResourceTypes: []string{"Handle"},
		States:        []string{"Open", "Closed"},
		Initial:       "Open",
		Transitions: []typechecker.ResourceTransitionDeclaration{
			{
				Name:       "inspect-transition",
				Callable:   "inspect",
				From:       "Open",
				To:         "Open",
				Parameters: []typechecker.ResourceParameterDeclaration{{Index: 0, Mode: typechecker.ResourceParameterBorrowed}},
			},
			{
				Name:       "update-transition",
				Callable:   "update",
				From:       "Open",
				To:         "Open",
				Parameters: []typechecker.ResourceParameterDeclaration{{Index: 0, Mode: typechecker.ResourceParameterBorrowedMut}},
			},
			{
				Name:       "close-transition",
				Callable:   "close",
				From:       "Open",
				To:         "Closed",
				Parameters: []typechecker.ResourceParameterDeclaration{{Index: 0, Mode: typechecker.ResourceParameterConsumed}},
			},
		},
	}}
}

func TestResourceSemIREmitsCanonicalParameterModes(t *testing.T) {
	const source = `
Handle: type = struct { id: u32 }
inspect: (h: Handle): () = {}
update: (h: Handle): () = {}
close: (h: Handle): () = {}
`

	result, err := New().
		WithSource("resource-modes.oak", source).
		ResourceSemIR(compilerParameterModeDeclarations()).
		Get()
	if err != nil {
		t.Fatalf("resource SemIR stage failed: %v", err)
	}
	transitions := result.Module.Protocols[0].Transitions
	if len(transitions) != 3 {
		t.Fatalf("unexpected transitions: %#v", transitions)
	}

	inspect, _, err := transitions[0].ResourceSemantics()
	if err != nil || len(inspect.Borrowed) != 1 || inspect.Borrowed[0] != 0 {
		t.Fatalf("inspect mode was not emitted canonically: %#v err=%v", inspect, err)
	}
	update, _, err := transitions[1].ResourceSemantics()
	if err != nil || len(update.BorrowedMut) != 1 || update.BorrowedMut[0] != 0 {
		t.Fatalf("update mode was not emitted canonically: %#v err=%v", update, err)
	}
	close, _, err := transitions[2].ResourceSemantics()
	if err != nil || len(close.Consumes) != 1 || close.Consumes[0] != 0 {
		t.Fatalf("close mode was not emitted canonically: %#v err=%v", close, err)
	}

	if transitions[0].Effects[0].Name != semir.ResourceEffectBorrow ||
		transitions[1].Effects[0].Name != semir.ResourceEffectBorrowMut ||
		transitions[2].Effects[0].Name != semir.ResourceEffectConsume {
		t.Fatalf("unexpected canonical effects: %#v", transitions)
	}
}

func TestDefaultCheckPreservesAuthorityAcrossBorrowModes(t *testing.T) {
	const source = `
Handle: type = struct { id: u32 }
inspect: (h: Handle): () = {}
update: (h: Handle): () = {}
close: (h: Handle): () = {}
f: (h: Handle): u32 {
  inspect(h)
  update(h)
  h.id
}
`

	if _, err := New().
		WithSource("borrowed-resource.oak", source).
		WithResourceProtocols(compilerParameterModeDeclarations()).
		Check().
		Get(); err != nil {
		t.Fatalf("borrowed resource authority should remain live: %v", err)
	}
}

func TestDefaultCheckConsumesOnlyConsumedMode(t *testing.T) {
	const source = `
Handle: type = struct { id: u32 }
inspect: (h: Handle): () = {}
update: (h: Handle): () = {}
close: (h: Handle): () = {}
f: (h: Handle): u32 {
  close(h)
  h.id
}
`

	_, err := New().
		WithSource("consumed-resource-mode.oak", source).
		WithResourceProtocols(compilerParameterModeDeclarations()).
		Check().
		Get()
	if err == nil {
		t.Fatal("expected consumed resource rejection")
	}
	var diagnosticErr *DiagnosticError
	if !errors.As(err, &diagnosticErr) {
		t.Fatalf("expected DiagnosticError, got %T: %v", err, err)
	}
	for _, diagnostic := range diagnosticErr.Diagnostics {
		if diagnostic != nil && diagnostic.Code == typechecker.CodeResourceUsedAfterConsume {
			return
		}
	}
	t.Fatalf("expected %s, got %#v", typechecker.CodeResourceUsedAfterConsume, diagnosticErr.Diagnostics)
}
