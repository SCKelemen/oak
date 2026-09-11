package typechecker

import (
	"strings"
	"testing"
)

func resourceTestModel() ResourceModel {
	model := NewResourceModel()
	model.MarkResourceType("Handle")
	model.MarkOperation("close", ResourceOperation{Consumes: []int{0}})
	model.MarkOperation("renew", ResourceOperation{Consumes: []int{0}, ReturnsFresh: true})
	return model
}

func resourceDiagnostics(tc *TypeChecker) []string {
	out := []string{}
	for _, d := range tc.Diagnostics() {
		if d.Code == CodeResourceUsedAfterConsume {
			out = append(out, d.PlainText())
		}
	}
	return out
}

func TestTypedResourceDirectUseAfterConsumingCall(t *testing.T) {
	input := `
Handle: type = struct { id: u32 }
close: (h: Handle): () = {}
f: (h: Handle): u32 {
  close(h)
  h.id
}`
	tc := setupTypeChecker(input)
	program := parseProgram(input)
	tc.CheckProgramWithResources(program, resourceTestModel())

	got := resourceDiagnostics(tc)
	if len(got) != 1 {
		t.Fatalf("expected one OAK-B0111 diagnostic, got %v (all errors: %v)", got, tc.Errors())
	}
	if !strings.Contains(got[0], "cannot be used after") {
		t.Fatalf("expected direct consumed-authority explanation, got %q", got[0])
	}
}

func TestTypedResourceConditionalConsumeJoinsToMaybeConsumed(t *testing.T) {
	input := `
Handle: type = struct { id: u32 }
close: (h: Handle): () = {}
f: (h: Handle, take: Bool): u32 {
  take ? {
    close(h)
  } | {}
  h.id
}`
	tc := setupTypeChecker(input)
	program := parseProgram(input)
	tc.CheckProgramWithResources(program, resourceTestModel())

	got := resourceDiagnostics(tc)
	if len(got) != 1 {
		t.Fatalf("expected one joined OAK-B0111 diagnostic, got %v (all errors: %v)", got, tc.Errors())
	}
	if !strings.Contains(got[0], "may have been consumed") || !strings.Contains(got[0], "control-flow join") {
		t.Fatalf("expected maybe-consumed join explanation, got %q", got[0])
	}
}

func TestTypedResourceBothBranchesConsumeIsDefinitelyConsumed(t *testing.T) {
	input := `
Handle: type = struct { id: u32 }
close: (h: Handle): () = {}
f: (h: Handle, take: Bool): u32 {
  take ? {
    close(h)
  } | {
    close(h)
  }
  h.id
}`
	tc := setupTypeChecker(input)
	program := parseProgram(input)
	tc.CheckProgramWithResources(program, resourceTestModel())

	got := resourceDiagnostics(tc)
	if len(got) != 1 {
		t.Fatalf("expected one OAK-B0111 diagnostic, got %v (all errors: %v)", got, tc.Errors())
	}
	if strings.Contains(got[0], "may have been consumed") {
		t.Fatalf("both consuming paths should join to definitely consumed, got %q", got[0])
	}
}

func TestTypedResourceAliasClassInvalidatesTogether(t *testing.T) {
	input := `
Handle: type = struct { id: u32 }
close: (h: Handle): () = {}
f: (h: Handle): u32 {
  alias: Handle = h
  close(alias)
  h.id
}`
	tc := setupTypeChecker(input)
	program := parseProgram(input)
	tc.CheckProgramWithResources(program, resourceTestModel())

	got := resourceDiagnostics(tc)
	if len(got) != 1 {
		t.Fatalf("expected alias-class OAK-B0111, got %v (all errors: %v)", got, tc.Errors())
	}
	if !strings.Contains(got[0], `alias "alias" derives authority from "h"`) {
		t.Fatalf("expected programmer-visible alias provenance, got %q", got[0])
	}
}

func TestTypedResourceFreshReturnDoesNotReviveOldBinding(t *testing.T) {
	input := `
Handle: type = struct { id: u32 }
renew: (h: Handle): Handle = Handle { id: h.id }
f: (h: Handle): u32 {
  next: Handle = renew(h)
  next.id
}`
	tc := setupTypeChecker(input)
	program := parseProgram(input)
	tc.CheckProgramWithResources(program, resourceTestModel())

	if got := resourceDiagnostics(tc); len(got) != 0 {
		t.Fatalf("fresh returned resource should be usable: %v", got)
	}
}

func TestTypedResourceShortCircuitConsumeIsConditional(t *testing.T) {
	input := `
Handle: type = struct { id: u32 }
close_bool: (h: Handle): Bool = true
f: (h: Handle, gate: Bool): u32 {
  gate && close_bool(h)
  h.id
}`
	model := resourceTestModel()
	model.MarkOperation("close_bool", ResourceOperation{Consumes: []int{0}})
	tc := setupTypeChecker(input)
	program := parseProgram(input)
	tc.CheckProgramWithResources(program, model)

	got := resourceDiagnostics(tc)
	if len(got) != 1 || !strings.Contains(got[0], "may have been consumed") {
		t.Fatalf("short-circuit RHS should join live and consumed paths, got %v (all errors: %v)", got, tc.Errors())
	}
}
