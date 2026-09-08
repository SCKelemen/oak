package typechecker

import (
	"strings"
	"testing"
)

func resourceCallModel(name string, parameters ...ResourceParameterDeclaration) ResourceModel {
	model := NewResourceModel()
	model.MarkResourceType("Handle")
	operation := ResourceOperation{Parameters: parameters}
	for _, parameter := range parameters {
		if parameter.Mode == ResourceParameterConsumed {
			operation.Consumes = append(operation.Consumes, parameter.Index)
		}
	}
	model.MarkOperation(name, operation)
	return model
}

func resourceCallDiagnostics(tc *TypeChecker, code string) []string {
	out := []string{}
	for _, d := range tc.Diagnostics() {
		if d.Code == code {
			out = append(out, d.PlainText())
		}
	}
	return out
}

func TestResourceCallSharedBorrowsMayAlias(t *testing.T) {
	input := `
Handle: type = struct { id: u32 }
inspect_pair: (left: Handle, right: Handle): () = {}
f: (h: Handle): u32 {
  alias: Handle = h
  inspect_pair(h, alias)
  h.id
}`
	model := resourceCallModel("inspect_pair",
		ResourceParameterDeclaration{Index: 0, Mode: ResourceParameterBorrowed},
		ResourceParameterDeclaration{Index: 1, Mode: ResourceParameterBorrowed},
	)
	tc := setupTypeChecker(input)
	tc.CheckProgramWithResources(parseProgram(input), model)

	if got := resourceCallDiagnostics(tc, CodeResourceCallAliasConflict); len(got) != 0 {
		t.Fatalf("shared resource borrows should be alias-compatible: %v", got)
	}
	if got := resourceCallDiagnostics(tc, CodeResourceUsedAfterConsume); len(got) != 0 {
		t.Fatalf("shared resource borrows must preserve permanent authority: %v", got)
	}
}

func TestResourceCallMutableBorrowRejectsAliasedParticipant(t *testing.T) {
	input := `
Handle: type = struct { id: u32 }
update_pair: (left: Handle, right: Handle): () = {}
f: (h: Handle): u32 {
  alias: Handle = h
  update_pair(h, alias)
  h.id
}`
	model := resourceCallModel("update_pair",
		ResourceParameterDeclaration{Index: 0, Mode: ResourceParameterBorrowedMut},
		ResourceParameterDeclaration{Index: 1, Mode: ResourceParameterBorrowed},
	)
	tc := setupTypeChecker(input)
	tc.CheckProgramWithResources(parseProgram(input), model)

	got := resourceCallDiagnostics(tc, CodeResourceCallAliasConflict)
	if len(got) != 1 {
		t.Fatalf("expected one %s diagnostic, got %v (all errors: %v)", CodeResourceCallAliasConflict, got, tc.Errors())
	}
	if !strings.Contains(got[0], "exclusive mutable") || !strings.Contains(got[0], `alias "alias" derives authority from "h"`) {
		t.Fatalf("expected exclusivity and alias provenance, got %q", got[0])
	}
}

func TestResourceCallConsumeAliasConflictDoesNotMutateAuthority(t *testing.T) {
	input := `
Handle: type = struct { id: u32 }
consume_and_read: (owned: Handle, read: Handle): () = {}
f: (h: Handle): u32 {
  alias: Handle = h
  consume_and_read(h, alias)
  h.id
}`
	model := resourceCallModel("consume_and_read",
		ResourceParameterDeclaration{Index: 0, Mode: ResourceParameterConsumed},
		ResourceParameterDeclaration{Index: 1, Mode: ResourceParameterBorrowed},
	)
	tc := setupTypeChecker(input)
	tc.CheckProgramWithResources(parseProgram(input), model)

	if got := resourceCallDiagnostics(tc, CodeResourceCallAliasConflict); len(got) != 1 {
		t.Fatalf("expected one call-alias conflict, got %v (all errors: %v)", got, tc.Errors())
	}
	if got := resourceCallDiagnostics(tc, CodeResourceUsedAfterConsume); len(got) != 0 {
		t.Fatalf("invalid call must not consume and cascade into %s: %v", CodeResourceUsedAfterConsume, got)
	}
}

func TestResourceCallDistinctConsumedArgumentsAreAllowed(t *testing.T) {
	input := `
Handle: type = struct { id: u32 }
consume_pair: (left: Handle, right: Handle): () = {}
f: (left: Handle, right: Handle): u32 {
  consume_pair(left, right)
  0
}`
	model := resourceCallModel("consume_pair",
		ResourceParameterDeclaration{Index: 0, Mode: ResourceParameterConsumed},
		ResourceParameterDeclaration{Index: 1, Mode: ResourceParameterConsumed},
	)
	tc := setupTypeChecker(input)
	tc.CheckProgramWithResources(parseProgram(input), model)

	if got := resourceCallDiagnostics(tc, CodeResourceCallAliasConflict); len(got) != 0 {
		t.Fatalf("distinct authority classes should satisfy consuming exclusivity: %v", got)
	}
}

func TestResourceCallSameBindingConflictsWithMutableBorrow(t *testing.T) {
	input := `
Handle: type = struct { id: u32 }
touch_pair: (left: Handle, right: Handle): () = {}
f: (h: Handle): u32 {
  touch_pair(h, h)
  h.id
}`
	model := resourceCallModel("touch_pair",
		ResourceParameterDeclaration{Index: 0, Mode: ResourceParameterBorrowedMut},
		ResourceParameterDeclaration{Index: 1, Mode: ResourceParameterBorrowed},
	)
	tc := setupTypeChecker(input)
	tc.CheckProgramWithResources(parseProgram(input), model)

	if got := resourceCallDiagnostics(tc, CodeResourceCallAliasConflict); len(got) != 1 {
		t.Fatalf("same binding must conflict with mutable call access: %v", got)
	}
}

func TestResourceCallMutableBorrowFailsClosedForFieldProjection(t *testing.T) {
	input := `
Handle: type = struct { id: u32 }
Holder: type = struct { handle: Handle }
update_pair: (left: Handle, right: Handle): () = {}
f: (holder: Holder): u32 {
  update_pair(holder.handle, holder.handle)
  holder.handle.id
}`
	model := resourceCallModel("update_pair",
		ResourceParameterDeclaration{Index: 0, Mode: ResourceParameterBorrowedMut},
		ResourceParameterDeclaration{Index: 1, Mode: ResourceParameterBorrowed},
	)
	tc := setupTypeChecker(input)
	tc.CheckProgramWithResources(parseProgram(input), model)

	got := resourceCallDiagnostics(tc, CodeResourceCallAliasConflict)
	if len(got) != 1 {
		t.Fatalf("untracked field projections must fail closed for exclusive access: %v (all errors: %v)", got, tc.Errors())
	}
	if !strings.Contains(got[0], "provenance is not traceable") {
		t.Fatalf("expected traceability diagnostic, got %q", got[0])
	}
}

func TestResourceCallConsumedFieldProjectionFailsClosed(t *testing.T) {
	input := `
Handle: type = struct { id: u32 }
Holder: type = struct { handle: Handle }
close: (h: Handle): () = {}
f: (holder: Holder): u32 {
  close(holder.handle)
  holder.handle.id
}`
	model := resourceCallModel("close",
		ResourceParameterDeclaration{Index: 0, Mode: ResourceParameterConsumed},
	)
	tc := setupTypeChecker(input)
	tc.CheckProgramWithResources(parseProgram(input), model)

	if got := resourceCallDiagnostics(tc, CodeResourceCallAliasConflict); len(got) != 1 {
		t.Fatalf("untracked consumed resource expression must fail closed: %v (all errors: %v)", got, tc.Errors())
	}
	if got := resourceCallDiagnostics(tc, CodeResourceUsedAfterConsume); len(got) != 0 {
		t.Fatalf("rejected untracked consumption must not invent permanent invalidation: %v", got)
	}
}

func TestResourceCallProjectionBindingsRetainUnknownProvenance(t *testing.T) {
	input := `
Handle: type = struct { id: u32 }
Holder: type = struct { handle: Handle }
update_pair: (left: Handle, right: Handle): () = {}
f: (holder: Holder): u32 {
  left: Handle = holder.handle
  right: Handle = holder.handle
  update_pair(left, right)
  holder.handle.id
}`
	model := resourceCallModel("update_pair",
		ResourceParameterDeclaration{Index: 0, Mode: ResourceParameterBorrowedMut},
		ResourceParameterDeclaration{Index: 1, Mode: ResourceParameterBorrowed},
	)
	tc := setupTypeChecker(input)
	tc.CheckProgramWithResources(parseProgram(input), model)

	got := resourceCallDiagnostics(tc, CodeResourceCallAliasConflict)
	if len(got) != 1 {
		t.Fatalf("bound untraceable projections must remain unknown: %v (all errors: %v)", got, tc.Errors())
	}
	if !strings.Contains(got[0], "provenance is not traceable") {
		t.Fatalf("expected retained unknown-provenance diagnostic, got %q", got[0])
	}
}

func TestResourceCallFreshReturnRemainsTrackedForExclusiveAccess(t *testing.T) {
	input := `
Handle: type = struct { id: u32 }
renew: (h: Handle): Handle = h
update_pair: (left: Handle, right: Handle): () = {}
f: (left: Handle, right: Handle): u32 {
  next: Handle = renew(left)
  update_pair(next, right)
  next.id
}`
	model := resourceCallModel("update_pair",
		ResourceParameterDeclaration{Index: 0, Mode: ResourceParameterBorrowedMut},
		ResourceParameterDeclaration{Index: 1, Mode: ResourceParameterBorrowed},
	)
	model.MarkOperation("renew", ResourceOperation{ReturnsFresh: true})
	tc := setupTypeChecker(input)
	tc.CheckProgramWithResources(parseProgram(input), model)

	if got := resourceCallDiagnostics(tc, CodeResourceCallAliasConflict); len(got) != 0 {
		t.Fatalf("explicit fresh return must introduce tracked independent authority: %v", got)
	}
}
