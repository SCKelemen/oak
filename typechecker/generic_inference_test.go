package typechecker

import (
	"strings"
	"testing"
)

func TestUnifyGenericAccumulatesDistinctBindings(t *testing.T) {
	u := NewUnifier()
	left := u.FreshTypeVar("T")
	right := u.FreshTypeVar("U")
	expected := &GenericType{Name: "Pair", TypeArgs: []Type{left, right}}
	actual := &GenericType{Name: "Pair", TypeArgs: []Type{
		&PrimitiveType{Name: "i32"},
		&StringType{},
	}}

	sub := u.Unify(expected, actual)
	if sub == nil {
		t.Fatalf("expected generic application to unify: %v", u.Errors())
	}
	if got := sub.Apply(left); !got.Equals(&PrimitiveType{Name: "i32"}) {
		t.Fatalf("T = %s, want i32", got)
	}
	if got := sub.Apply(right); !got.Equals(&StringType{}) {
		t.Fatalf("U = %s, want string", got)
	}
}

func TestUnifyGenericRepeatedVariableIsConsistent(t *testing.T) {
	u := NewUnifier()
	repeated := u.FreshTypeVar("T")
	expected := &GenericType{Name: "Pair", TypeArgs: []Type{repeated, repeated}}
	actual := &GenericType{Name: "Pair", TypeArgs: []Type{
		&PrimitiveType{Name: "i32"},
		&PrimitiveType{Name: "i32"},
	}}

	sub := u.Unify(expected, actual)
	if sub == nil {
		t.Fatalf("expected repeated binding to unify: %v", u.Errors())
	}
	if got := sub.Apply(repeated); !got.Equals(&PrimitiveType{Name: "i32"}) {
		t.Fatalf("T = %s, want i32", got)
	}
}

func TestUnifyGenericRejectsConflictingRepeatedVariable(t *testing.T) {
	u := NewUnifier()
	repeated := u.FreshTypeVar("T")
	expected := &GenericType{Name: "Pair", TypeArgs: []Type{repeated, repeated}}
	actual := &GenericType{Name: "Pair", TypeArgs: []Type{
		&PrimitiveType{Name: "i32"},
		&StringType{},
	}}

	if sub := u.Unify(expected, actual); sub != nil {
		t.Fatalf("conflicting repeated binding unexpectedly unified: %#v", sub)
	}
}

func TestUnifyRecordAccumulatesRepeatedBindings(t *testing.T) {
	u := NewUnifier()
	repeated := u.FreshTypeVar("T")
	expected := &RecordType{Fields: map[string]Type{
		"left":  repeated,
		"right": repeated,
	}}
	actual := &RecordType{Fields: map[string]Type{
		"left":  &PrimitiveType{Name: "i32"},
		"right": &StringType{},
	}}

	if sub := u.Unify(expected, actual); sub != nil {
		t.Fatalf("conflicting record binding unexpectedly unified: %#v", sub)
	}
}

func TestGenericCallInfersMultipleTypeParameters(t *testing.T) {
	input := `
fn [T, U] second(first: T, value: U) -> U { value }
left: i32 = i32(1)
right: string = "oak"
result: string = second(left, right)
`
	if errs := checkGenericShapeSource(t, input); len(errs) != 0 {
		t.Fatalf("unexpected errors: %v", errs)
	}
}

func TestGenericCallRejectsRepeatedParameterConflict(t *testing.T) {
	input := `
fn [T] same(left: T, right: T) -> T { left }
left: i32 = i32(1)
right: string = "oak"
result: i32 = same(left, right)
`
	errs := checkGenericShapeSource(t, input)
	if len(errs) == 0 {
		t.Fatal("expected repeated generic parameter conflict")
	}
	if !strings.Contains(strings.Join(errs, "\n"), "argument 2") {
		t.Fatalf("unexpected errors: %v", errs)
	}
}

func TestGenericCallInfersFieldAccessorResult(t *testing.T) {
	input := `
Person: type = struct { name: i32, age: u8 }
fn [T, U] project(selector: (T) -> U, value: T) -> U { selector(value) }
person: Person = Person { name: 42, age: 7 }
result: i32 = project(.name, person)
`
	if errs := checkGenericShapeSource(t, input); len(errs) != 0 {
		t.Fatalf("unexpected errors: %v", errs)
	}
}
