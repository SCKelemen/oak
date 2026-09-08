package semir

import (
	"strings"
	"testing"
)

func TestResourceTransitionSemanticsDecodesParameterModes(t *testing.T) {
	transition := Transition{
		Callable: "operate",
		Effects: []Effect{
			ResourceBorrowArgument(2),
			ResourceConsumeArgument(0),
			ResourceBorrowMutArgument(1),
			ResourceReturnFresh(),
		},
	}

	semantics, present, err := transition.ResourceSemantics()
	if err != nil || !present {
		t.Fatalf("resource parameter modes did not decode: present=%v err=%v", present, err)
	}
	if len(semantics.Borrowed) != 1 || semantics.Borrowed[0] != 2 {
		t.Fatalf("borrowed arguments = %v", semantics.Borrowed)
	}
	if len(semantics.BorrowedMut) != 1 || semantics.BorrowedMut[0] != 1 {
		t.Fatalf("mutable borrowed arguments = %v", semantics.BorrowedMut)
	}
	if len(semantics.Consumes) != 1 || semantics.Consumes[0] != 0 {
		t.Fatalf("consumed arguments = %v", semantics.Consumes)
	}
	if !semantics.ReturnsFresh {
		t.Fatal("fresh result authority was lost")
	}
}

func TestResourceTransitionSemanticsRejectsConflictingParameterModes(t *testing.T) {
	transition := Transition{
		Callable: "operate",
		Effects: []Effect{
			ResourceBorrowArgument(0),
			ResourceConsumeArgument(0),
		},
	}

	_, present, err := transition.ResourceSemantics()
	if !present || err == nil || !strings.Contains(err.Error(), "both borrow and consume modes") {
		t.Fatalf("expected conflicting parameter-mode rejection, got present=%v err=%v", present, err)
	}
}

func TestResourceTransitionSemanticsRejectsMalformedBorrowIndex(t *testing.T) {
	transition := Transition{
		Callable: "inspect",
		Effects: []Effect{{
			Namespace:  ResourceEffectNamespace,
			Name:       ResourceEffectBorrow,
			Parameters: []string{"arg:nope"},
		}},
	}

	_, present, err := transition.ResourceSemantics()
	if !present || err == nil || !strings.Contains(err.Error(), "invalid argument index") {
		t.Fatalf("expected malformed borrow rejection, got present=%v err=%v", present, err)
	}
}
