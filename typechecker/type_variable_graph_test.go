package typechecker

import (
	"reflect"
	"testing"
)

func TestTypeVariableWalkVisitsSharedGraphOnce(t *testing.T) {
	calls := 0
	walkTypeVariables(variableCoverageDAG(24), func(*TypeVar) bool { calls++; return false })
	if calls != 1 {
		t.Fatalf("visited the same binder %d times", calls)
	}
}

func TestTypeVariableWalkHasStableRecordOrder(t *testing.T) {
	a, z := &TypeVar{Name: "A"}, &TypeVar{Name: "Z"}
	r := &RecordType{Fields: map[string]Type{"z": z, "a": a}}
	for i := 0; i < 100; i++ {
		if got := typeVarsIn(r); !reflect.DeepEqual(got, []*TypeVar{a, z}) {
			t.Fatal("anonymous record traversal depends on map iteration")
		}
	}
	r.Order = []string{"z", "a"}
	if got := typeVarsIn(r); !reflect.DeepEqual(got, []*TypeVar{z, a}) {
		t.Fatal("declared record traversal lost field order")
	}
}

func TestTypeVariableWalkStopsEarly(t *testing.T) {
	a, b := &TypeVar{Name: "T"}, &TypeVar{Name: "T"}
	typ := &FunctionType{Parameters: []Type{a}, ReturnType: b}
	calls := 0
	if !walkTypeVariables(typ, func(v *TypeVar) bool { calls++; return v == a }) || calls != 1 {
		t.Fatal("walk did not stop at the matching binder")
	}
	if got := typeVarsIn(typ); !reflect.DeepEqual(got, []*TypeVar{a, b}) {
		t.Fatal("walk conflated same-name binders")
	}
}
