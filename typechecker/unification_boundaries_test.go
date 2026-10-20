package typechecker

import "testing"

func TestUnificationRecordBoundaries(t *testing.T) {
	emptyToken := &RecordType{Name: "Token", Struct: true}
	emptyShape := &RecordType{}
	openShape := &RecordType{Open: true, Row: "r"}
	field := map[string]Type{"x": &PrimitiveType{Name: "u8"}}
	cases := []struct {
		name        string
		left, right Type
		want        bool
	}{
		{"empty nominal versus shape", emptyToken, emptyShape, false},
		{"empty nominal versus unit", emptyToken, &UnitType{}, false},
		{"empty open versus closed", openShape, emptyShape, false},
		{"nonempty open versus closed", &RecordType{Fields: field, Open: true}, &RecordType{Fields: field}, false},
		{"same nominal token", emptyToken, &RecordType{Name: "Token", Struct: true}, true},
		{"semantic empty versus unit", emptyShape, &UnitType{}, true},
		{"nonempty nominal versus shape", &RecordType{Name: "Stored", Struct: true, Fields: field}, &RecordType{Fields: field}, true},
		{"diagnostic row names", openShape, &RecordType{Open: true, Row: "s"}, true},
	}
	wrappers := []struct {
		name string
		wrap func(Type) Type
	}{
		{"direct", func(x Type) Type { return x }},
		{"function", func(x Type) Type { return &FunctionType{Parameters: []Type{x}, ReturnType: &UnitType{}} }},
		{"array", func(x Type) Type { return &ArrayType{Length: 2, ElementType: x} }},
		{"generic", func(x Type) Type { return &GenericType{Name: "Box", TypeArgs: []Type{x}} }},
		{"record", func(x Type) Type { return &RecordType{Fields: map[string]Type{"value": x}} }},
	}
	for _, c := range cases {
		for _, w := range wrappers {
			t.Run(c.name+"/"+w.name, func(t *testing.T) {
				for _, pair := range [][2]Type{{c.left, c.right}, {c.right, c.left}} {
					u := NewUnifier()
					if got := u.Unify(w.wrap(pair[0]), w.wrap(pair[1])) != nil; got != c.want {
						t.Fatalf("unified = %v, want %v; errors %v", got, c.want, u.Errors())
					}
				}
			})
		}
	}
}

func TestUnificationDoesNotEraseRepeatedNominalBinder(t *testing.T) {
	v := NewUnifier().FreshTypeVar("T")
	left := &FunctionType{Parameters: []Type{v, v}, ReturnType: &UnitType{}}
	right := &FunctionType{Parameters: []Type{&RecordType{Name: "Token", Struct: true}, &RecordType{}}, ReturnType: &UnitType{}}
	if NewUnifier().Unify(left, right) != nil {
		t.Fatal("one binder accepted both a nominal token and a structural empty record")
	}
	if v.Monomorphic != nil {
		t.Fatal("failed unification mutated binder state")
	}
}
