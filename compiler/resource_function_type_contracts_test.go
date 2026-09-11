package compiler

import (
	"testing"

	"github.com/SCKelemen/oak/semir"
	"github.com/SCKelemen/oak/typechecker"
)

// Contracts on function types (docs/spec/50-borrowing.md section 9,
// authority roadmap milestone 2): a function-typed parameter may require a
// callable contract of the values passed for it. A consuming function does
// not satisfy a borrowed requirement, an uncontracted or unknown function
// value satisfies no requirement with a mode, an exactly matching function
// is accepted, and inside the callee a call through the parameter uses the
// declared contract instead of being unknown.
func functionTypeDeclarations() []typechecker.ResourceProtocolDeclaration {
	borrowedCallable := &typechecker.ResourceCallableContract{
		Parameters: []typechecker.ResourceParameterDeclaration{{Index: 0, Mode: typechecker.ResourceParameterBorrowed}},
	}
	return []typechecker.ResourceProtocolDeclaration{{
		Name:          "HandleLifecycle",
		ResourceTypes: []string{"Handle"},
		States:        []string{"Open", "Closed"},
		Initial:       "Open",
		Transitions: []typechecker.ResourceTransitionDeclaration{
			{Name: "inspect", Callable: "inspect", From: "Open", To: "Open",
				Parameters: []typechecker.ResourceParameterDeclaration{{Index: 0, Mode: typechecker.ResourceParameterBorrowed}}},
			{Name: "close", Callable: "close", From: "Open", To: "Closed",
				Parameters: []typechecker.ResourceParameterDeclaration{{Index: 0, Mode: typechecker.ResourceParameterConsumed}}},
			// with_each borrows its handle and requires a borrowed callable
			{Name: "with_each", Callable: "with_each", From: "Open", To: "Open",
				Parameters: []typechecker.ResourceParameterDeclaration{
					{Index: 0, Callable: borrowedCallable},
					{Index: 1, Mode: typechecker.ResourceParameterBorrowed},
				}},
		},
	}}
}

const functionTypeBase = `
Handle: type = struct { id: u32 }
inspect: (h: Handle): () = {}
close: (h: Handle): () = {}
plain: (h: Handle): () = {}
with_each: (op: (Handle) -> (), h: Handle): u32 {
  op(h)
  op(h)
  h.id
}
`

func checkFunctionTypes(t *testing.T, name, body string) error {
	t.Helper()
	_, err := New().
		WithSource(name+".oak", functionTypeBase+body).
		WithResourceProtocols(functionTypeDeclarations()).
		Check().
		Get()
	return err
}

func TestFunctionTypeContractAcceptsMatchingFunction(t *testing.T) {
	// with_each's body calls op twice: the declared borrowed contract keeps
	// h live (no OAK-B0115, no OAK-B0111), and inspect matches exactly.
	if err := checkFunctionTypes(t, "matching", `
f: (h: Handle): u32 {
  n: u32 = with_each(inspect, h)
  h.id + n
}
`); err != nil {
		t.Fatalf("a borrowed function should satisfy a borrowed callable contract: %v", err)
	}
}

func TestFunctionTypeContractRejectsConsumingFunction(t *testing.T) {
	expectCode(t, "consuming", checkFunctionTypes(t, "consuming", `
f: (h: Handle): u32 = with_each(close, h)
`), typechecker.CodeResourceCallableContractMismatch)
}

func TestFunctionTypeContractRejectsUncontractedAndUnknownValues(t *testing.T) {
	// plain has no contract: it does not satisfy a borrowed requirement.
	expectCode(t, "uncontracted", checkFunctionTypes(t, "uncontracted", `
f: (h: Handle): u32 = with_each(plain, h)
`), typechecker.CodeResourceCallableContractMismatch)
	// A function-typed parameter without a declared contract is unknown.
	expectCode(t, "unknown", checkFunctionTypes(t, "unknown", `
g: (op: (Handle) -> (), h: Handle): u32 = with_each(op, h)
`), typechecker.CodeResourceCallableContractMismatch)
}

func TestFunctionTypeContractCarriesThroughFunctionValues(t *testing.T) {
	// A local bound from inspect carries inspect's contract and matches.
	if err := checkFunctionTypes(t, "carried", `
f: (h: Handle): u32 {
  look: (Handle) -> () = inspect
  with_each(look, h)
}
`); err != nil {
		t.Fatalf("a function value bound from a matching function should be accepted: %v", err)
	}
}

func TestFunctionTypeContractRoundTripsThroughSemIR(t *testing.T) {
	result, err := New().
		WithSource("callable-semir.oak", functionTypeBase).
		ResourceSemIR(functionTypeDeclarations()).
		Get()
	if err != nil {
		t.Fatalf("resource SemIR stage failed: %v", err)
	}
	semantics, _, err := result.Module.Protocols[0].Transitions[2].ResourceSemantics()
	if err != nil || len(semantics.Callables) != 1 || semantics.Callables[0].Argument != 0 ||
		len(semantics.Callables[0].Borrowed) != 1 || semantics.Callables[0].Borrowed[0] != 0 {
		t.Fatalf("callable contract not encoded: %#v err=%v", semantics, err)
	}
	if semantics.Borrowed[0] != 1 {
		t.Fatalf("the handle parameter mode shifted: %#v", semantics)
	}
	model, err := typechecker.ResourceModelFromSemIR(result.Module)
	if err != nil {
		t.Fatalf("model from SemIR: %v", err)
	}
	op := model.Operations["with_each"]
	var found *typechecker.ResourceCallableContract
	for _, p := range op.Parameters {
		if p.Index == 0 {
			found = p.Callable
		}
	}
	if found == nil || len(found.Parameters) != 1 || found.Parameters[0].Mode != typechecker.ResourceParameterBorrowed {
		t.Fatalf("callable contract lost on the way back from SemIR: %#v", op)
	}
	_ = semir.ResourceEffectCallableBorrow
}

func TestFunctionTypeContractRequiresFunctionParameter(t *testing.T) {
	bad := []typechecker.ResourceProtocolDeclaration{{
		Name: "HandleLifecycle", ResourceTypes: []string{"Handle"}, States: []string{"Open"}, Initial: "Open",
		Transitions: []typechecker.ResourceTransitionDeclaration{
			{Name: "inspect", Callable: "inspect", From: "Open", To: "Open",
				Parameters: []typechecker.ResourceParameterDeclaration{{Index: 0, Callable: &typechecker.ResourceCallableContract{}}}},
		},
	}}
	_, err := New().
		WithSource("bad-callable.oak", "Handle: type = struct { id: u32 }\ninspect: (h: Handle): () = {}\n").
		WithResourceProtocols(bad).
		Check().
		Get()
	if err == nil {
		t.Fatal("a callable contract on a non-function parameter must be rejected")
	}
}
