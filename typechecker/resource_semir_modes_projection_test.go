package typechecker

import (
	"testing"

	"github.com/SCKelemen/oak/semir"
)

func TestResourceModelFromSemIRPreservesParameterModes(t *testing.T) {
	module := resourceSemanticModule()
	module.Protocols[0].Transitions = append(module.Protocols[0].Transitions, semir.Transition{
		Name:     "AccessPairTransition",
		Callable: "access_pair",
		From:     "Open",
		To:       "Open",
		Effects: []semir.Effect{
			semir.ResourceBorrowMutArgument(1),
			semir.ResourceBorrowArgument(0),
		},
	})

	model, err := ResourceModelFromSemIR(module)
	if err != nil {
		t.Fatalf("resource model derivation failed: %v", err)
	}
	op, ok := model.Operations["access_pair"]
	if !ok {
		t.Fatal("expected resource operation for resolved callable")
	}
	want := []ResourceParameterDeclaration{
		{Index: 0, Mode: ResourceParameterBorrowed},
		{Index: 1, Mode: ResourceParameterBorrowedMut},
	}
	if len(op.Parameters) != len(want) {
		t.Fatalf("unexpected parameter modes: %#v", op.Parameters)
	}
	for i := range want {
		if op.Parameters[i] != want[i] {
			t.Fatalf("parameter modes were not preserved and sorted: got %#v want %#v", op.Parameters, want)
		}
	}
	if len(op.Consumes) != 0 {
		t.Fatalf("borrow modes must not invent permanent consumption: %#v", op)
	}
}
