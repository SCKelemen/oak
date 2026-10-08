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
	if NewUnifier().Unify(a, b) != nil {
		t.Fatal("distinct nominal empty structs unified")
	}
}

// Equals remains a compatibility relation for nonempty structural shapes;
// these pairwise laws do not claim transitivity through a semantic shape or
// symmetry of directional assignability and record-shape satisfaction.
func TestRecordEqualsNominalBoundary(t *testing.T) {
	record := func(name string, nominal bool, fields map[string]Type) *RecordType {
		return &RecordType{Name: name, Struct: nominal, Fields: fields}
	}
	empty := record("", false, nil)
	namedEmpty := record("EmptyShape", false, nil)
	anonymousStruct := record("", true, nil)
	a := record("EmptyA", true, nil)
	b := record("EmptyB", true, nil)
	fields := map[string]Type{"x": &PrimitiveType{Name: "u8"}}
	shape := record("", false, fields)
	stored := record("Stored", true, fields)
	tests := []struct {
		name        string
		left, right Type
		want        bool
	}{
		{"distinct empty nominal types", a, b, false},
		{"same empty nominal identity", a, record("EmptyA", true, map[string]Type{}), true},
		{"empty nominal and anonymous semantic record", a, empty, false},
		{"empty nominal and named semantic record", a, namedEmpty, false},
		{"empty nominal and same-named semantic record", a, record("EmptyA", false, nil), false},
		{"empty nominal and anonymous struct", a, anonymousStruct, false},
		{"empty nominal and unit", a, &UnitType{}, false},
		{"semantic empty names are structural", empty, namedEmpty, true},
		{"anonymous empty struct remains structural", empty, anonymousStruct, true},
		{"semantic empty record and unit", empty, &UnitType{}, true},
		{"named semantic empty record and unit", namedEmpty, &UnitType{}, true},
		{"empty and nonempty semantic records", empty, shape, false},
		{"empty semantic and nonempty nominal", empty, stored, false},
		{"empty nominal and nonempty semantic", a, shape, false},
		{"distinct nonempty nominal types", stored, record("OtherStored", true, fields), false},
		{"same nonempty nominal identity", stored, record("Stored", true, fields), true},
		{"nonempty nominal and semantic shape compatibility", stored, shape, true},
		{"nonempty semantic names are structural", shape, record("Shape", false, fields), true},
		{"nonempty record and unit", shape, &UnitType{}, false},
		{"byte alias field", shape, record("", false, map[string]Type{"x": &PrimitiveType{Name: "byte"}}), true},
		{"rune alias field", record("", false, map[string]Type{"x": &PrimitiveType{Name: "rune"}}), record("", false, map[string]Type{"x": &PrimitiveType{Name: "u32"}}), true},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if !tt.left.Equals(tt.left) || !tt.right.Equals(tt.right) {
				t.Fatal("record compatibility lost reflexivity")
			}
			if got := tt.left.Equals(tt.right); got != tt.want {
				t.Errorf("left.Equals(right) = %v, want %v", got, tt.want)
			}
			if got := tt.right.Equals(tt.left); got != tt.want {
				t.Errorf("right.Equals(left) = %v, want %v", got, tt.want)
			}
		})
	}
}
