package typechecker

import (
	"strings"
	"testing"
)

func checkedResourceProgram(t *testing.T, input string) *TypeChecker {
	t.Helper()
	tc := setupTypeChecker(input)
	program := parseProgram(input)
	tc.CheckProgram(program)
	if errors := tc.Errors(); len(errors) != 0 {
		t.Fatalf("test program failed ordinary type checking: %v", errors)
	}
	return tc
}

func handleResourceDeclarations() []ResourceProtocolDeclaration {
	return []ResourceProtocolDeclaration{{
		Name:          "HandleLifecycle",
		ResourceTypes: []string{"Handle"},
		States:        []string{"Open", "Closed"},
		Initial:       "Open",
		Transitions: []ResourceTransitionDeclaration{
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

func TestResolveResourceDeclarationsBindsCheckedTypesAndCallables(t *testing.T) {
	const input = `
Handle: type = struct { id: u32 }
close: (h: Handle): () = {}
renew: (h: Handle): Handle = Handle { id: h.id }
`
	tc := checkedResourceProgram(t, input)
	resolved, err := tc.ResolveResourceDeclarations(handleResourceDeclarations())
	if err != nil {
		t.Fatalf("resource resolution failed: %v", err)
	}
	if len(resolved.Types) != 1 || resolved.Types[0].Name != "Handle" || resolved.Types[0].Protocol != "HandleLifecycle" {
		t.Fatalf("unexpected resolved resource types: %#v", resolved.Types)
	}
	if len(resolved.Protocols) != 1 || len(resolved.Protocols[0].Transitions) != 2 {
		t.Fatalf("unexpected resolved protocols: %#v", resolved.Protocols)
	}
	closeTransition := resolved.Protocols[0].Transitions[0]
	if closeTransition.Name != "close-transition" || closeTransition.Callable != "close" {
		t.Fatalf("transition label must stay distinct from resolved callable: %#v", closeTransition)
	}
	if len(closeTransition.Consumes) != 1 || closeTransition.Consumes[0] != 0 || closeTransition.ReturnsFresh {
		t.Fatalf("unexpected close semantics: %#v", closeTransition)
	}
	if !resolved.Protocols[0].Transitions[1].ReturnsFresh {
		t.Fatal("renew transition should return fresh authority")
	}
}

func TestResolveResourceDeclarationsRequiresExplicitCallableBinding(t *testing.T) {
	const input = `
Handle: type = struct { id: u32 }
close: (h: Handle): () = {}
`
	tc := checkedResourceProgram(t, input)
	declarations := handleResourceDeclarations()
	declarations[0].Transitions = declarations[0].Transitions[:1]
	declarations[0].Transitions[0].Callable = ""

	_, err := tc.ResolveResourceDeclarations(declarations)
	if err == nil || !strings.Contains(err.Error(), "no resolved callable binding") {
		t.Fatalf("expected missing callable rejection, got %v", err)
	}
}

func TestResolveResourceDeclarationsRejectsUnknownCallable(t *testing.T) {
	const input = `
Handle: type = struct { id: u32 }
`
	tc := checkedResourceProgram(t, input)
	declarations := handleResourceDeclarations()
	declarations[0].Transitions = declarations[0].Transitions[:1]
	declarations[0].Transitions[0].Callable = "missing"

	_, err := tc.ResolveResourceDeclarations(declarations)
	if err == nil || !strings.Contains(err.Error(), `unknown callable "missing"`) {
		t.Fatalf("expected unknown callable rejection, got %v", err)
	}
}

func TestResolveResourceDeclarationsRejectsNonResourceConsumedArgument(t *testing.T) {
	const input = `
Handle: type = struct { id: u32 }
close_id: (id: u32): () = {}
`
	tc := checkedResourceProgram(t, input)
	declarations := []ResourceProtocolDeclaration{{
		Name:          "HandleLifecycle",
		ResourceTypes: []string{"Handle"},
		States:        []string{"Open", "Closed"},
		Initial:       "Open",
		Transitions: []ResourceTransitionDeclaration{{
			Name:     "close-transition",
			Callable: "close_id",
			From:     "Open",
			To:       "Closed",
			Consumes: []int{0},
		}},
	}}

	_, err := tc.ResolveResourceDeclarations(declarations)
	if err == nil || !strings.Contains(err.Error(), "non-resource type") {
		t.Fatalf("expected non-resource consumed argument rejection, got %v", err)
	}
}

func TestResolveResourceDeclarationsRejectsFreshNonResourceReturn(t *testing.T) {
	const input = `
Handle: type = struct { id: u32 }
finish: (h: Handle): u32 = h.id
`
	tc := checkedResourceProgram(t, input)
	declarations := []ResourceProtocolDeclaration{{
		Name:          "HandleLifecycle",
		ResourceTypes: []string{"Handle"},
		States:        []string{"Open"},
		Initial:       "Open",
		Transitions: []ResourceTransitionDeclaration{{
			Name:         "finish-transition",
			Callable:     "finish",
			From:         "Open",
			To:           "Open",
			Consumes:     []int{0},
			ReturnsFresh: true,
		}},
	}}

	_, err := tc.ResolveResourceDeclarations(declarations)
	if err == nil || !strings.Contains(err.Error(), "fresh return") {
		t.Fatalf("expected non-resource fresh return rejection, got %v", err)
	}
}

func TestResolveResourceDeclarationsRejectsConsumeIndexOutsideSignature(t *testing.T) {
	const input = `
Handle: type = struct { id: u32 }
close: (h: Handle): () = {}
`
	tc := checkedResourceProgram(t, input)
	declarations := handleResourceDeclarations()
	declarations[0].Transitions = declarations[0].Transitions[:1]
	declarations[0].Transitions[0].Consumes = []int{1}

	_, err := tc.ResolveResourceDeclarations(declarations)
	if err == nil || !strings.Contains(err.Error(), "outside its 1 parameters") {
		t.Fatalf("expected consume index rejection, got %v", err)
	}
}

func TestResolveResourceDeclarationsRejectsConflictingCallableSemantics(t *testing.T) {
	const input = `
Left: type = struct { id: u32 }
Right: type = struct { id: u32 }
transfer: (left: Left, right: Right): () = {}
`
	tc := checkedResourceProgram(t, input)
	declarations := []ResourceProtocolDeclaration{
		{
			Name:          "LeftLifecycle",
			ResourceTypes: []string{"Left"},
			States:        []string{"Live"},
			Initial:       "Live",
			Transitions: []ResourceTransitionDeclaration{{
				Name: "left-transfer", Callable: "transfer", From: "Live", To: "Live", Consumes: []int{0},
			}},
		},
		{
			Name:          "RightLifecycle",
			ResourceTypes: []string{"Right"},
			States:        []string{"Live"},
			Initial:       "Live",
			Transitions: []ResourceTransitionDeclaration{{
				Name: "right-transfer", Callable: "transfer", From: "Live", To: "Live", Consumes: []int{1},
			}},
		},
	}

	_, err := tc.ResolveResourceDeclarations(declarations)
	if err == nil || !strings.Contains(err.Error(), "conflicting semantics") {
		t.Fatalf("expected conflicting callable semantics rejection, got %v", err)
	}
}
