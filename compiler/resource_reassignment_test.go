package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/typechecker"
)

// Resource provenance through reassignment (docs/spec/50-borrowing.md
// section 9, authority roadmap milestone 3): a rebound name denotes its new
// value's authority. Alias reassignment makes later exclusive use conflict,
// fresh assignment revives no old alias, shadowing leaves outer bindings
// alone, branches cannot manufacture disjointness, and a value of unknown
// provenance fails closed on exclusive use.
func reassignmentDeclarations() []typechecker.ResourceProtocolDeclaration {
	mode := func(index int, m typechecker.ResourceParameterMode) typechecker.ResourceParameterDeclaration {
		return typechecker.ResourceParameterDeclaration{Index: index, Mode: m}
	}
	return []typechecker.ResourceProtocolDeclaration{{
		Name:          "HandleLifecycle",
		ResourceTypes: []string{"Handle"},
		States:        []string{"Open", "Closed"},
		Initial:       "Open",
		Transitions: []typechecker.ResourceTransitionDeclaration{
			{Name: "open", Callable: "open", From: "Open", To: "Open", ReturnsFresh: true},
			{Name: "inspect", Callable: "inspect", From: "Open", To: "Open", Parameters: []typechecker.ResourceParameterDeclaration{mode(0, typechecker.ResourceParameterBorrowed)}},
			{Name: "close", Callable: "close", From: "Open", To: "Closed", Parameters: []typechecker.ResourceParameterDeclaration{mode(0, typechecker.ResourceParameterConsumed)}},
			{Name: "update_pair", Callable: "update_pair", From: "Open", To: "Open", Parameters: []typechecker.ResourceParameterDeclaration{
				mode(0, typechecker.ResourceParameterBorrowedMut), mode(1, typechecker.ResourceParameterBorrowed)}},
		},
	}}
}

const reassignmentBase = `
Handle: type = struct { id: u32 }
open: (id: u32): Handle = Handle { id: id }
inspect: (h: Handle): () = {}
close: (h: Handle): () = {}
update_pair: (left: Handle, right: Handle): () = {}
project: (h: Handle): Handle = h
`

func checkReassignment(t *testing.T, name, body string) error {
	t.Helper()
	_, err := New().
		WithSource(name+".oak", reassignmentBase+body).
		WithResourceProtocols(reassignmentDeclarations()).
		Check().
		Get()
	return err
}

func TestReassignmentAliasConflicts(t *testing.T) {
	// After `alias = h`, an exclusive pairing of the two names conflicts.
	expectCode(t, "alias-conflict", checkReassignment(t, "alias-conflict", `
f: (h: Handle, other: Handle): u32 {
  alias: Handle = other
  alias = h
  update_pair(h, alias)
  0
}
`), typechecker.CodeResourceCallAliasConflict)
	// Consuming through the rebound name consumes the shared authority.
	expectCode(t, "alias-consume", checkReassignment(t, "alias-consume", `
f: (h: Handle, other: Handle): u32 {
  alias: Handle = other
  alias = h
  close(alias)
  h.id
}
`), typechecker.CodeResourceUsedAfterConsume)
	// The old alias class is left alone: other stays usable.
	if err := checkReassignment(t, "old-class-untouched", `
f: (h: Handle, other: Handle): u32 {
  alias: Handle = other
  alias = h
  close(alias)
  inspect(other)
  other.id
}
`); err != nil {
		t.Fatalf("rebinding must not invalidate the alias's old class: %v", err)
	}
}

func TestReassignmentFreshDoesNotReviveOldAliases(t *testing.T) {
	// h consumed, then h = open(..): h is a new live authority, but twin
	// (an alias of the old h) is still consumed.
	if err := checkReassignment(t, "fresh-live", `
f: (h: Handle): u32 {
  close(h)
  h = open(u32(2))
  inspect(h)
  h.id
}
`); err != nil {
		t.Fatalf("a fresh assignment must give the name live authority: %v", err)
	}
	expectCode(t, "fresh-no-revive", checkReassignment(t, "fresh-no-revive", `
f: (h: Handle): u32 {
  twin: Handle = h
  close(h)
  h = open(u32(2))
  twin.id
}
`), typechecker.CodeResourceUsedAfterConsume)
}

func TestReassignmentShadowingLeavesOuterBindingsAlone(t *testing.T) {
	// Oak rejects redeclaring a visible name (the no-shadowing rule of
	// docs/spec/83-modules.md section 7), so a shadowing binding can never
	// touch the outer authority: the case holds by construction.
	err := checkReassignment(t, "shadowing", `
f: (h: Handle, other: Handle): u32 {
  ok: Bool = true
  ok ? {
    h: Handle = other
    close(h)
  } | { }
  inspect(h)
  h.id
}
`)
	if err == nil || !strings.Contains(err.Error(), "already declared") {
		t.Fatalf("expected the redeclaration rule to reject the inner h, got %v", err)
	}
	// A distinct inner name aliasing other leaves h untouched after the block.
	if err := checkReassignment(t, "inner-alias", `
f: (h: Handle, other: Handle): u32 {
  ok: Bool = true
  ok ? {
    inner: Handle = other
    inspect(inner)
  } | { }
  inspect(h)
  h.id
}
`); err != nil {
		t.Fatalf("an inner alias of another handle must leave h alone: %v", err)
	}
}

func TestReassignmentBranchesCannotManufactureDisjointness(t *testing.T) {
	// On one path alias denotes h, on the other it denotes other: after the
	// join its provenance is unknown, so an exclusive pairing with h fails
	// closed rather than being accepted as distinct.
	expectCode(t, "branch-join", checkReassignment(t, "branch-join", `
f: (h: Handle, other: Handle, flag: Bool): u32 {
  alias: Handle = other
  flag ? { alias = h } | { }
  update_pair(h, alias)
  0
}
`), typechecker.CodeResourceCallAliasConflict)
}

func TestReassignmentFromUnknownProvenanceFailsClosed(t *testing.T) {
	// project(h) returns a resource with no fresh-return fact: the rebound
	// name has unknown provenance, and consuming it fails closed.
	expectCode(t, "unknown", checkReassignment(t, "unknown", `
f: (h: Handle): u32 {
  h = project(h)
  close(h)
  0
}
`), typechecker.CodeResourceCallAliasConflict)
}

func TestReassignmentReleasesEntryAuthority(t *testing.T) {
	// A borrowed parameter rebound to a fresh handle may consume the new
	// value: the entry authority governed the old one.
	borrowedPeek := reassignmentDeclarations()
	borrowedPeek[0].Transitions = append(borrowedPeek[0].Transitions, typechecker.ResourceTransitionDeclaration{
		Name: "peek", Callable: "peek", From: "Open", To: "Open",
		Parameters: []typechecker.ResourceParameterDeclaration{{Index: 0, Mode: typechecker.ResourceParameterBorrowed}},
	})
	_, err := New().
		WithSource("release.oak", reassignmentBase+`
peek: (h: Handle): u32 {
  h = open(u32(3))
  close(h)
  0
}
`).
		WithResourceProtocols(borrowedPeek).
		Check().
		Get()
	if err != nil {
		t.Fatalf("a rebound parameter's new value is not governed by its entry mode: %v", err)
	}
}
