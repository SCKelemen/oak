package compiler

import (
	"errors"
	"testing"

	"github.com/SCKelemen/oak/typechecker"
)

func compilerCloseResourceDeclarations() []typechecker.ResourceProtocolDeclaration {
	declarations := compilerResourceDeclarations()
	declarations[0].Transitions = declarations[0].Transitions[:1]
	return declarations
}

func requireResourceUseAfterConsume(t *testing.T, err error) {
	t.Helper()
	if err == nil {
		t.Fatal("expected resource use-after-consume rejection")
	}
	var diagnosticErr *DiagnosticError
	if !errors.As(err, &diagnosticErr) {
		t.Fatalf("expected first-class DiagnosticError, got %T: %v", err, err)
	}
	if diagnosticErr.Phase != "resource" {
		t.Fatalf("expected resource phase rejection, got %q", diagnosticErr.Phase)
	}
	for _, diagnostic := range diagnosticErr.Diagnostics {
		if diagnostic != nil && diagnostic.Code == typechecker.CodeResourceUsedAfterConsume {
			return
		}
	}
	t.Fatalf("expected %s in resource diagnostics: %#v", typechecker.CodeResourceUsedAfterConsume, diagnosticErr.Diagnostics)
}

func TestCheckRunsConfiguredResourceSemantics(t *testing.T) {
	const source = `
Handle: type = struct { id: u32 }
close: (h: Handle): () = {}
f: (h: Handle): u32 {
  close(h)
  h.id
}
`

	_, err := New().
		WithSource("default-resource.oak", source).
		WithResourceProtocols(compilerCloseResourceDeclarations()).
		Check().
		Get()
	requireResourceUseAfterConsume(t, err)
}

func TestCheckConfiguredFreshReturnCarriesNewAuthority(t *testing.T) {
	const source = `
Handle: type = struct { id: u32 }
close: (h: Handle): () = {}
renew: (h: Handle): Handle = Handle { id: h.id }
f: (h: Handle): u32 {
  next: Handle = renew(h)
  next.id
}
`

	if _, err := New().
		WithSource("default-resource-fresh.oak", source).
		WithResourceProtocols(compilerResourceDeclarations()).
		Check().
		Get(); err != nil {
		t.Fatalf("configured resource semantics should accept fresh returned authority: %v", err)
	}
}

func TestWithResourceProtocolsPreservesCompilationValueSemantics(t *testing.T) {
	const source = `
Handle: type = struct { id: u32 }
close: (h: Handle): () = {}
f: (h: Handle): u32 {
  close(h)
  h.id
}
`

	declarations := compilerCloseResourceDeclarations()
	base := New().WithSource("resource-copy.oak", source)
	configured := base.WithResourceProtocols(declarations)

	// Mutating the caller-owned declaration graph after configuration must not
	// alter the immutable Compilation value.
	declarations[0].ResourceTypes[0] = "Missing"
	declarations[0].Transitions[0].Callable = "missing"
	declarations[0].Transitions[0].Consumes[0] = 99

	_, configuredErr := configured.Check().Get()
	requireResourceUseAfterConsume(t, configuredErr)

	if _, err := base.Check().Get(); err != nil {
		t.Fatalf("unconfigured compilation unexpectedly inherited resource semantics: %v", err)
	}
}
