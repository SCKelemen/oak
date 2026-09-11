package compiler

import (
	"testing"

	"github.com/SCKelemen/oak/semir"
	"github.com/SCKelemen/oak/typechecker"
)

// Receiver authority is its own slot (docs/spec/50-borrowing.md section 9,
// authority roadmap milestone 2): a method's receiver carries a mode of its
// own — borrowed, borrowed-mut, or consumed — that never shifts the
// explicit argument indices. A consuming receiver invalidates the caller's
// handle, a borrowed receiver leaves it live, a mutable receiver and a
// borrowed argument naming one resource conflict, and a method body is
// checked under its receiver's entry authority.
func receiverDeclarations() []typechecker.ResourceProtocolDeclaration {
	return []typechecker.ResourceProtocolDeclaration{{
		Name:          "HandleLifecycle",
		ResourceTypes: []string{"Handle"},
		States:        []string{"Open", "Closed"},
		Initial:       "Open",
		Transitions: []typechecker.ResourceTransitionDeclaration{
			{Name: "peek", Callable: "Handle::peek", From: "Open", To: "Open", Receiver: typechecker.ResourceParameterBorrowed},
			{Name: "close", Callable: "Handle::close", From: "Open", To: "Closed", Receiver: typechecker.ResourceParameterConsumed},
			{Name: "merge", Callable: "Handle::merge", From: "Open", To: "Open", Receiver: typechecker.ResourceParameterBorrowedMut,
				Parameters: []typechecker.ResourceParameterDeclaration{{Index: 0, Mode: typechecker.ResourceParameterBorrowed}}},
			{Name: "leak", Callable: "Handle::leak", From: "Open", To: "Open", Receiver: typechecker.ResourceParameterBorrowed},
		},
	}}
}

const receiverBase = `
Handle: type = Open: u32 | Closed
fn (h: Handle) peek(): u32 = u32(1)
fn (h: Handle) close(): () = {}
fn (h: Handle) merge(other: Handle): () = {}
`

func checkReceivers(t *testing.T, name, body string) error {
	t.Helper()
	_, err := New().
		WithSource(name+".oak", receiverBase+body).
		WithResourceProtocols(receiverDeclarations()).
		Check().
		Get()
	return err
}

func TestReceiverModes(t *testing.T) {
	// A consuming receiver invalidates the handle.
	expectCode(t, "consumed-receiver", checkReceivers(t, "consumed-receiver", `
fn (h: Handle) leak(): () = {}
f: (h: Handle): u32 {
  h.close()
  h.peek()
}
`), typechecker.CodeResourceUsedAfterConsume)
	// A borrowed receiver leaves it live, and a mutable receiver with a
	// distinct borrowed argument is fine.
	if err := checkReceivers(t, "borrowed-receiver", `
fn (h: Handle) leak(): () = {}
f: (h: Handle, g: Handle): u32 {
  h.peek()
  h.merge(g)
  h.peek()
}
`); err != nil {
		t.Fatalf("borrowed and mutable receivers should keep authority: %v", err)
	}
	// The mutable receiver and a borrowed argument naming one resource
	// conflict (OAK-B0112), and the argument keeps index 0: the receiver did
	// not shift it.
	expectCode(t, "receiver-alias", checkReceivers(t, "receiver-alias", `
fn (h: Handle) leak(): () = {}
f: (h: Handle): u32 {
  h.merge(h)
  h.peek()
}
`), typechecker.CodeResourceCallAliasConflict)
	// A method body is checked under its receiver's entry authority: a
	// borrowed receiver may not be consumed inside the method.
	expectCode(t, "receiver-entry", checkReceivers(t, "receiver-entry", `
fn (h: Handle) leak(): () {
  h.close()
}
`), typechecker.CodeResourceParameterForwarded)
}

func TestReceiverModeRoundTripsThroughSemIR(t *testing.T) {
	result, err := New().
		WithSource("receiver-semir.oak", receiverBase+"fn (h: Handle) leak(): () = {}\n").
		ResourceSemIR(receiverDeclarations()).
		Get()
	if err != nil {
		t.Fatalf("resource SemIR stage failed: %v", err)
	}
	transitions := result.Module.Protocols[0].Transitions
	semantics, _, err := transitions[1].ResourceSemantics()
	if err != nil || semantics.Receiver != semir.ResourceEffectConsume {
		t.Fatalf("close receiver not encoded as consume: %#v err=%v", semantics, err)
	}
	merge, _, err := transitions[2].ResourceSemantics()
	if err != nil || merge.Receiver != semir.ResourceEffectBorrowMut || len(merge.Borrowed) != 1 || merge.Borrowed[0] != 0 {
		t.Fatalf("merge receiver or argument not encoded: %#v err=%v", merge, err)
	}
	model, err := typechecker.ResourceModelFromSemIR(result.Module)
	if err != nil {
		t.Fatalf("model from SemIR: %v", err)
	}
	if op := model.Operations["Handle::close"]; op.Receiver != typechecker.ResourceParameterConsumed {
		t.Fatalf("receiver mode lost on the way back from SemIR: %#v", op)
	}
}

func TestReceiverModeRequiresMethodOnResource(t *testing.T) {
	bad := []typechecker.ResourceProtocolDeclaration{{
		Name: "HandleLifecycle", ResourceTypes: []string{"Handle"}, States: []string{"Open"}, Initial: "Open",
		Transitions: []typechecker.ResourceTransitionDeclaration{
			{Name: "free", Callable: "free", From: "Open", To: "Open", Receiver: typechecker.ResourceParameterBorrowed},
		},
	}}
	_, err := New().
		WithSource("bad-receiver.oak", "Handle: type = Open: u32 | Closed\nfree: (h: Handle): () = {}\n").
		WithResourceProtocols(bad).
		Check().
		Get()
	if err == nil {
		t.Fatal("a receiver mode on a plain function must be rejected")
	}
}
