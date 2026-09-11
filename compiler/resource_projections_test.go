package compiler

import (
	"testing"

	"github.com/SCKelemen/oak/typechecker"
)

// Resource provenance through record projections and aggregate writes
// (docs/spec/50-borrowing.md section 9, authority roadmap milestone 3): a
// record built from a literal gives each resource field the provenance of
// its initializer, projections are uses of that field's authority,
// aggregate writes rebind the field, whole-record reassignment rebinds
// every field, and fields of records without provenance stay untracked so
// exclusive or consuming use of them fails closed.
const projectionBase = `
Handle: type = struct { id: u32 }
Box: type = struct { inner: Handle, tag: u32 }
Pair: type = struct { left: Box, right: Handle }
open: (id: u32): Handle = Handle { id: id }
inspect: (h: Handle): () = {}
close: (h: Handle): () = {}
update_pair: (left: Handle, right: Handle): () = {}
`

func checkProjections(t *testing.T, name, body string) error {
	t.Helper()
	_, err := New().
		WithSource(name+".oak", projectionBase+body).
		WithResourceProtocols(reassignmentDeclarations()).
		Check().
		Get()
	return err
}

func TestProjectionAliasesItsInitializer(t *testing.T) {
	// Consuming through b.inner consumes h.
	expectCode(t, "projection-consume", checkProjections(t, "projection-consume", `
f: (h: Handle): u32 {
  b: Box = Box { inner: h, tag: u32(1) }
  close(b.inner)
  h.id
}
`), typechecker.CodeResourceUsedAfterConsume)
	// And consuming h invalidates the projection.
	expectCode(t, "projection-after", checkProjections(t, "projection-after", `
f: (h: Handle): u32 {
  b: Box = Box { inner: h, tag: u32(1) }
  close(h)
  inspect(b.inner)
  0
}
`), typechecker.CodeResourceUsedAfterConsume)
	// Exclusive pairing of a handle with its own projection conflicts.
	expectCode(t, "projection-alias", checkProjections(t, "projection-alias", `
f: (h: Handle): u32 {
  b: Box = Box { inner: h, tag: u32(1) }
  update_pair(h, b.inner)
  0
}
`), typechecker.CodeResourceCallAliasConflict)
	// A fresh field is independent authority, usable and consumable.
	if err := checkProjections(t, "projection-fresh", `
f: (h: Handle): u32 {
  b: Box = Box { inner: open(u32(2)), tag: u32(1) }
  update_pair(h, b.inner)
  close(b.inner)
  h.id
}
`); err != nil {
		t.Fatalf("a fresh field is its own authority: %v", err)
	}
}

func TestProjectionNestedPaths(t *testing.T) {
	expectCode(t, "nested", checkProjections(t, "nested", `
f: (h: Handle, g: Handle): u32 {
  b: Box = Box { inner: h, tag: u32(1) }
  p: Pair = Pair { left: b, right: g }
  close(p.left.inner)
  h.id
}
`), typechecker.CodeResourceUsedAfterConsume)
}

func TestAggregateWriteRebindsField(t *testing.T) {
	// b.inner = g: the field now denotes g; h is untouched.
	expectCode(t, "write-alias", checkProjections(t, "write-alias", `
f: (h: Handle, g: Handle): u32 {
  b: Box = Box { inner: h, tag: u32(1) }
  b.inner = g
  close(b.inner)
  inspect(h)
  g.id
}
`), typechecker.CodeResourceUsedAfterConsume)
	if err := checkProjections(t, "write-keeps-old", `
f: (h: Handle, g: Handle): u32 {
  b: Box = Box { inner: h, tag: u32(1) }
  b.inner = g
  close(b.inner)
  inspect(h)
  h.id
}
`); err != nil {
		t.Fatalf("rebinding a field must not touch the old field value's authority: %v", err)
	}
	// Whole-record reassignment rebinds every field.
	expectCode(t, "record-rebind", checkProjections(t, "record-rebind", `
f: (h: Handle, g: Handle): u32 {
  b: Box = Box { inner: h, tag: u32(1) }
  c: Box = Box { inner: g, tag: u32(2) }
  b = c
  close(b.inner)
  g.id
}
`), typechecker.CodeResourceUsedAfterConsume)
}

func TestUnknownRecordFieldsFailClosed(t *testing.T) {
	// A record parameter's fields have no provenance: consuming one fails
	// closed, and pairing two of them exclusively cannot prove them distinct.
	expectCode(t, "parameter-field", checkProjections(t, "parameter-field", `
f: (b: Box): u32 {
  close(b.inner)
  0
}
`), typechecker.CodeResourceCallAliasConflict)
	expectCode(t, "parameter-pair", checkProjections(t, "parameter-pair", `
f: (p: Pair): u32 {
  update_pair(p.left.inner, p.right)
  0
}
`), typechecker.CodeResourceCallAliasConflict)
}
