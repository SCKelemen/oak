package compiler

import (
	"errors"
	"testing"

	"github.com/SCKelemen/oak/typechecker"
)

func compilerResourceCallExclusivityDeclarations() []typechecker.ResourceProtocolDeclaration {
	return []typechecker.ResourceProtocolDeclaration{{
		Name:          "HandleAccess",
		ResourceTypes: []string{"Handle"},
		States:        []string{"Open"},
		Initial:       "Open",
		Transitions: []typechecker.ResourceTransitionDeclaration{{
			Name:     "update-pair",
			Callable: "update_pair",
			From:     "Open",
			To:       "Open",
			Parameters: []typechecker.ResourceParameterDeclaration{
				{Index: 0, Mode: typechecker.ResourceParameterBorrowedMut},
				{Index: 1, Mode: typechecker.ResourceParameterBorrowed},
			},
		}},
	}}
}

func TestDefaultCheckRejectsAliasedMutableResourceArguments(t *testing.T) {
	const source = `
Handle: type = struct { id: u32 }
update_pair: (left: Handle, right: Handle): () = {}
f: (h: Handle): u32 {
  alias: Handle = h
  update_pair(h, alias)
  h.id
}
`

	_, err := New().
		WithSource("resource-call-alias.oak", source).
		WithResourceProtocols(compilerResourceCallExclusivityDeclarations()).
		Check().
		Get()
	if err == nil {
		t.Fatal("expected aliased mutable resource call rejection")
	}
	var diagnosticErr *DiagnosticError
	if !errors.As(err, &diagnosticErr) {
		t.Fatalf("expected DiagnosticError, got %T: %v", err, err)
	}
	if diagnosticErr.Phase != "resource" {
		t.Fatalf("expected resource phase rejection, got %q", diagnosticErr.Phase)
	}

	aliasConflicts := 0
	consumedErrors := 0
	for _, diagnostic := range diagnosticErr.Diagnostics {
		if diagnostic == nil {
			continue
		}
		switch diagnostic.Code {
		case typechecker.CodeResourceCallAliasConflict:
			aliasConflicts++
		case typechecker.CodeResourceUsedAfterConsume:
			consumedErrors++
		}
	}
	if aliasConflicts != 1 {
		t.Fatalf("expected one %s diagnostic, got %#v", typechecker.CodeResourceCallAliasConflict, diagnosticErr.Diagnostics)
	}
	if consumedErrors != 0 {
		t.Fatalf("call-local alias conflict must not cascade into %s: %#v", typechecker.CodeResourceUsedAfterConsume, diagnosticErr.Diagnostics)
	}
}
