package compiler

import (
	"errors"
	"testing"

	"github.com/SCKelemen/oak/typechecker"
)

func compilerResourceDeclarations() []typechecker.ResourceProtocolDeclaration {
	return []typechecker.ResourceProtocolDeclaration{{
		Name:          "HandleLifecycle",
		ResourceTypes: []string{"Handle"},
		States:        []string{"Open", "Closed"},
		Initial:       "Open",
		Transitions: []typechecker.ResourceTransitionDeclaration{
			{
				Name:     "close-transition",
				Callable: "close",
				From:     "Open",
				To:       "Closed",
				Consumes: []int{0},
			},
			{
				Name:         "renew-transition",
				Callable:     "renew",
				From:         "Open",
				To:           "Open",
				Consumes:     []int{0},
				ReturnsFresh: true,
			},
		},
	}}
}

func TestResourceSemIREmitsResolvedAuthorityAndCallableEffects(t *testing.T) {
	const source = `
Handle: type = struct { id: u32 }
close: (h: Handle): () = {}
renew: (h: Handle): Handle = h
f: (h: Handle): u32 {
  next: Handle = renew(h)
  next.id
}
`

	result, err := New().
		WithSource("resource.oak", source).
		ResourceSemIR(compilerResourceDeclarations()).
		Get()
	if err != nil {
		t.Fatalf("resource SemIR stage failed: %v", err)
	}
	if result == nil || result.Model == nil {
		t.Fatal("expected checked semantic result")
	}
	if len(result.Module.Definitions) != 1 {
		t.Fatalf("expected one resource definition, got %#v", result.Module.Definitions)
	}
	definition := result.Module.Definitions[0]
	if definition.Name != "Handle" || definition.Protocol != "HandleLifecycle" {
		t.Fatalf("unexpected resource definition: %#v", definition)
	}
	if definition.Authority.Resource != "live" || definition.Authority.Ownership != "owned" {
		t.Fatalf("resource authority was not emitted canonically: %#v", definition.Authority)
	}
	if len(result.Module.Protocols) != 1 || len(result.Module.Protocols[0].Transitions) != 2 {
		t.Fatalf("unexpected emitted protocols: %#v", result.Module.Protocols)
	}
	closeTransition := result.Module.Protocols[0].Transitions[0]
	if closeTransition.Name != "close-transition" || closeTransition.Callable != "close" {
		t.Fatalf("protocol label must not replace resolved callable identity: %#v", closeTransition)
	}
	semantics, present, err := closeTransition.ResourceSemantics()
	if err != nil || !present {
		t.Fatalf("emitted close effects did not decode: present=%v err=%v", present, err)
	}
	if len(semantics.Consumes) != 1 || semantics.Consumes[0] != 0 || semantics.ReturnsFresh {
		t.Fatalf("unexpected emitted close semantics: %#v", semantics)
	}
	renewSemantics, present, err := result.Module.Protocols[0].Transitions[1].ResourceSemantics()
	if err != nil || !present || !renewSemantics.ReturnsFresh {
		t.Fatalf("expected canonical fresh-return effect, got present=%v semantics=%#v err=%v", present, renewSemantics, err)
	}
}

func TestResourceSemIRFeedsEmittedModuleIntoPathSensitiveChecking(t *testing.T) {
	const source = `
Handle: type = struct { id: u32 }
close: (h: Handle): () = {}
renew: (h: Handle): Handle = h
f: (h: Handle): u32 {
  close(h)
  h.id
}
`

	_, err := New().
		WithSource("consumed.oak", source).
		ResourceSemIR(compilerResourceDeclarations()).
		Get()
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
	found := false
	for _, diagnostic := range diagnosticErr.Diagnostics {
		if diagnostic != nil && string(diagnostic.Code) == typechecker.CodeResourceUsedAfterConsume {
			found = true
			break
		}
	}
	if !found {
		t.Fatalf("expected %s in resource diagnostics: %#v", typechecker.CodeResourceUsedAfterConsume, diagnosticErr.Diagnostics)
	}
}

func TestResourceSemIRFreshReturnCarriesNewAuthority(t *testing.T) {
	const source = `
Handle: type = struct { id: u32 }
close: (h: Handle): () = {}
renew: (h: Handle): Handle = h
f: (h: Handle): u32 {
  next: Handle = renew(h)
  next.id
}
`

	if _, err := New().
		WithSource("fresh.oak", source).
		ResourceSemIR(compilerResourceDeclarations()).
		Get(); err != nil {
		t.Fatalf("fresh returned resource should remain usable: %v", err)
	}
}

func TestResourceSemIRRejectsUnresolvedSemanticInputBeforeEmission(t *testing.T) {
	const source = `
Handle: type = struct { id: u32 }
close: (h: Handle): () = {}
`
	declarations := compilerResourceDeclarations()
	declarations[0].Transitions = declarations[0].Transitions[:1]
	declarations[0].Transitions[0].Callable = ""

	_, err := New().
		WithSource("unresolved.oak", source).
		ResourceSemIR(declarations).
		Get()
	if err == nil {
		t.Fatal("expected unresolved resource declaration rejection")
	}
}
