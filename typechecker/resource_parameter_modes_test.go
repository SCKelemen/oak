package typechecker

import (
	"strings"
	"testing"
)

func TestResolveResourceDeclarationsNormalizesParameterModes(t *testing.T) {
	const input = `
Handle: type = struct { id: u32 }
operate: (read: Handle, write: Handle, close: Handle): Handle = read
`
	tc := checkedResourceProgram(t, input)
	declarations := []ResourceProtocolDeclaration{{
		Name:          "HandleLifecycle",
		ResourceTypes: []string{"Handle"},
		States:        []string{"Open", "Closed"},
		Initial:       "Open",
		Transitions: []ResourceTransitionDeclaration{{
			Name:     "operate-transition",
			Callable: "operate",
			From:     "Open",
			To:       "Open",
			Parameters: []ResourceParameterDeclaration{
				{Index: 2, Mode: ResourceParameterConsumed},
				{Index: 0, Mode: ResourceParameterBorrowed},
				{Index: 1, Mode: ResourceParameterBorrowedMut},
			},
			ReturnsFresh: true,
		}},
	}}

	resolved, err := tc.ResolveResourceDeclarations(declarations)
	if err != nil {
		t.Fatalf("resource resolution failed: %v", err)
	}
	transition := resolved.Protocols[0].Transitions[0]
	if len(transition.Parameters) != 3 {
		t.Fatalf("resolved parameter modes = %#v", transition.Parameters)
	}
	want := []ResolvedResourceParameter{
		{Index: 0, Mode: ResourceParameterBorrowed},
		{Index: 1, Mode: ResourceParameterBorrowedMut},
		{Index: 2, Mode: ResourceParameterConsumed},
	}
	for i := range want {
		if transition.Parameters[i] != want[i] {
			t.Fatalf("parameter %d = %#v, want %#v", i, transition.Parameters[i], want[i])
		}
	}
	if len(transition.Consumes) != 1 || transition.Consumes[0] != 2 {
		t.Fatalf("permanent-authority projection = %v", transition.Consumes)
	}
}

func TestResolveResourceDeclarationsKeepsLegacyConsumesCompatible(t *testing.T) {
	const input = `
Handle: type = struct { id: u32 }
close: (h: Handle): () = {}
`
	tc := checkedResourceProgram(t, input)
	declarations := handleResourceDeclarations()
	declarations[0].Transitions = declarations[0].Transitions[:1]

	resolved, err := tc.ResolveResourceDeclarations(declarations)
	if err != nil {
		t.Fatalf("legacy consume input failed: %v", err)
	}
	transition := resolved.Protocols[0].Transitions[0]
	if len(transition.Parameters) != 1 || transition.Parameters[0].Mode != ResourceParameterConsumed || transition.Parameters[0].Index != 0 {
		t.Fatalf("legacy consume was not normalized: %#v", transition.Parameters)
	}
}

func TestResolveResourceDeclarationsRejectsLegacyModeOverlap(t *testing.T) {
	const input = `
Handle: type = struct { id: u32 }
close: (h: Handle): () = {}
`
	tc := checkedResourceProgram(t, input)
	declarations := handleResourceDeclarations()
	declarations[0].Transitions = declarations[0].Transitions[:1]
	declarations[0].Transitions[0].Parameters = []ResourceParameterDeclaration{{Index: 0, Mode: ResourceParameterBorrowed}}

	_, err := tc.ResolveResourceDeclarations(declarations)
	if err == nil || !strings.Contains(err.Error(), "both parameter modes and legacy consumes") {
		t.Fatalf("expected compatibility-overlap rejection, got %v", err)
	}
}

func TestResolveResourceDeclarationsRejectsBorrowedNonResourceArgument(t *testing.T) {
	const input = `
Handle: type = struct { id: u32 }
inspect_id: (id: u32): () = {}
`
	tc := checkedResourceProgram(t, input)
	declarations := []ResourceProtocolDeclaration{{
		Name:          "HandleLifecycle",
		ResourceTypes: []string{"Handle"},
		States:        []string{"Open"},
		Initial:       "Open",
		Transitions: []ResourceTransitionDeclaration{{
			Name:       "inspect-transition",
			Callable:   "inspect_id",
			From:       "Open",
			To:         "Open",
			Parameters: []ResourceParameterDeclaration{{Index: 0, Mode: ResourceParameterBorrowed}},
		}},
	}}

	_, err := tc.ResolveResourceDeclarations(declarations)
	if err == nil || !strings.Contains(err.Error(), "non-resource type") {
		t.Fatalf("expected non-resource borrowed argument rejection, got %v", err)
	}
}
