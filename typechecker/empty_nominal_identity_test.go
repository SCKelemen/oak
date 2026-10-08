package typechecker

import "testing"

func TestEmptyNominalStructIdentity(t *testing.T) {
	a := &RecordType{Name: "EmptyA", Struct: true, Fields: map[string]Type{}}
	b := &RecordType{Name: "EmptyB", Struct: true, Fields: map[string]Type{}}
	unit := &UnitType{}
	empty := &RecordType{Fields: map[string]Type{}}
	if a.Equals(b) || b.Equals(a) || a.Equals(unit) || unit.Equals(a) || a.Equals(empty) || empty.Equals(a) {
		t.Fatal("nominal empty struct lost its identity")
	}
	if !a.Equals(a) || !empty.Equals(unit) || !unit.Equals(empty) {
		t.Fatal("nominal reflexivity or unit/semantic-record equivalence regressed")
	}
	if NewUnifier().Unify(a,b) != nil {
		t.Fatal("distinct nominal empty structs unified")
	}
}
