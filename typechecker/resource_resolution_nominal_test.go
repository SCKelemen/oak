package typechecker

import (
	"strings"
	"testing"
)

func TestResolveResourceDeclarationsRejectsStructuralRecordResourceType(t *testing.T) {
	const input = `
Handle: type = { id: u32 }
close: (h: Handle): () = {}
`
	tc := checkedResourceProgram(t, input)
	declarations := []ResourceProtocolDeclaration{{
		Name:          "HandleLifecycle",
		ResourceTypes: []string{"Handle"},
		States:        []string{"Open", "Closed"},
		Initial:       "Open",
		Transitions: []ResourceTransitionDeclaration{{
			Name:     "close-transition",
			Callable: "close",
			From:     "Open",
			To:       "Closed",
			Consumes: []int{0},
		}},
	}}

	_, err := tc.ResolveResourceDeclarations(declarations)
	if err == nil || !strings.Contains(err.Error(), "concrete nominal Oak type") {
		t.Fatalf("expected structural resource type rejection, got %v", err)
	}
}
