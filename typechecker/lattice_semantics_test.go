package typechecker

import "testing"

func TestIsSubtype_MeetProjectionAndIntroduction(t *testing.T) {
	i32 := &PrimitiveType{Name: "i32"}
	u8 := &PrimitiveType{Name: "u8"}
	any := &AnyType{}

	meet := &IntersectionType{Types: []Type{i32, u8}}
	if !IsSubtype(meet, i32) {
		t.Fatal("A & B must be a subtype of A")
	}
	if !IsSubtype(meet, u8) {
		t.Fatal("A & B must be a subtype of B")
	}

	meetWithTop := &IntersectionType{Types: []Type{i32, any}}
	if !IsSubtype(i32, meetWithTop) {
		t.Fatal("A must be a subtype of A & any")
	}

	if IsSubtype(i32, meet) {
		t.Fatal("A must not be a subtype of A & unrelated B")
	}
}

func TestIsSubtype_JoinInjectionAndElimination(t *testing.T) {
	i32 := &PrimitiveType{Name: "i32"}
	u8 := &PrimitiveType{Name: "u8"}
	join := &UnionType{Types: []Type{i32, u8}}

	if !IsSubtype(i32, join) {
		t.Fatal("A must be a subtype of A | B")
	}
	if !IsSubtype(u8, join) {
		t.Fatal("B must be a subtype of A | B")
	}
	if IsSubtype(join, i32) {
		t.Fatal("A | B must not be a subtype of A when B is unrelated")
	}
}

func TestIsSubtype_DistributiveLatticeReasoning(t *testing.T) {
	p := &PrimitiveType{Name: "p"}
	q := &PrimitiveType{Name: "q"}
	r := &PrimitiveType{Name: "r"}

	// (p | q) & (p | r) = p | (q & r) in the free distributive lattice.
	left := &IntersectionType{Types: []Type{
		&UnionType{Types: []Type{p, q}},
		&UnionType{Types: []Type{p, r}},
	}}
	right := &UnionType{Types: []Type{
		p,
		&IntersectionType{Types: []Type{q, r}},
	}}

	if !IsSubtype(left, right) {
		t.Fatal("distributed meet must subtype its equivalent join form")
	}
	if !IsSubtype(right, left) {
		t.Fatal("distributed join must subtype its equivalent meet form")
	}
}

func TestIsSubtype_BottomAndTop(t *testing.T) {
	i32 := &PrimitiveType{Name: "i32"}
	never := &NeverType{}
	any := &AnyType{}

	if !IsSubtype(never, i32) {
		t.Fatal("never must be bottom")
	}
	if !IsSubtype(i32, any) {
		t.Fatal("any must be top")
	}
	if IsSubtype(any, i32) {
		t.Fatal("top must not subtype an unrelated atom")
	}
	if IsSubtype(i32, never) {
		t.Fatal("an inhabited atom must not subtype bottom")
	}
}

func TestAssignableComposesLatticeWithRepresentationRules(t *testing.T) {
	tc := setupTypeChecker("")
	u8 := &PrimitiveType{Name: "u8"}
	u16 := &PrimitiveType{Name: "u16"}
	refinedU16 := &PrimitiveType{Name: "u16", Refinement: "Small"}
	any := &AnyType{}
	union := &UnionType{Types: []Type{u8, &BoolType{}}}
	intersection := &IntersectionType{Types: []Type{u8, &BoolType{}}}

	tests := []struct {
		name   string
		value  Type
		target Type
		want   bool
	}{
		{name: "bottom enters an ordinary type", value: &NeverType{}, target: u8, want: true},
		{name: "bottom enters restricted top without a value", value: &NeverType{}, target: any, want: true},
		{name: "top does not invent a runtime box", value: u8, target: any, want: false},
		{name: "join does not invent a runtime tag", value: u8, target: union, want: false},
		{name: "meet projection needs a representation", value: intersection, target: u8, want: false},
		{name: "same lattice type retains its representation", value: union, target: union, want: true},
		{name: "numeric widening", value: u8, target: u16, want: true},
		{name: "numeric narrowing", value: u16, target: u8, want: false},
		{name: "refinement erases to its base", value: refinedU16, target: u16, want: true},
		{name: "base requires checked refinement construction", value: u16, target: refinedU16, want: false},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			if got := tc.isAssignable(test.value, test.target); got != test.want {
				t.Fatalf("isAssignable(%s, %s) = %v, want %v", test.value, test.target, got, test.want)
			}
		})
	}
}

func TestAssignableKeepsStructuralAndAlignmentRelationsSeparate(t *testing.T) {
	tc := setupTypeChecker("")
	u8 := &PrimitiveType{Name: "u8"}
	source := &RecordType{Fields: map[string]Type{"x": u8, "y": u8}}
	target := &RecordType{Fields: map[string]Type{"x": u8}, Open: true}
	missing := &RecordType{Fields: map[string]Type{"z": u8}, Open: true}
	if !tc.isAssignable(source, target) || tc.isAssignable(source, missing) {
		t.Fatal("open-record shape satisfaction did not remain directional")
	}

	plain := &ArrayType{ElementType: u8, IsSpan: true}
	aligned := &ArrayType{ElementType: u8, IsSpan: true, Align: 64}
	if !tc.isAssignable(aligned, plain) || tc.isAssignable(plain, aligned) {
		t.Fatal("span alignment assignability did not remain directional")
	}
}

func TestIsSubtypeExhaustiveAgainstThreeAtomSemantics(t *testing.T) {
	atoms := []Type{
		&PrimitiveType{Name: "u8"},
		&BoolType{},
		&StringType{},
	}
	bySize := map[int][]Type{
		1: {&NeverType{}, &AnyType{}, atoms[0], atoms[1], atoms[2]},
	}
	for size := 3; size <= 5; size += 2 {
		for leftSize := 1; leftSize < size; leftSize += 2 {
			rightSize := size - leftSize - 1
			for _, left := range bySize[leftSize] {
				for _, right := range bySize[rightSize] {
					bySize[size] = append(bySize[size],
						&UnionType{Types: []Type{left, right}},
						&IntersectionType{Types: []Type{left, right}},
					)
				}
			}
		}
	}
	formulas := append(append(append([]Type{}, bySize[1]...), bySize[3]...), bySize[5]...)
	for _, left := range formulas {
		for _, right := range formulas {
			want := true
			for valuation := uint8(0); valuation < 1<<len(atoms); valuation++ {
				if latticeFormulaHolds(left, atoms, valuation) && !latticeFormulaHolds(right, atoms, valuation) {
					want = false
					break
				}
			}
			if got := IsSubtype(left, right); got != want {
				t.Fatalf("IsSubtype(%s, %s) = %v, pointwise containment = %v", left, right, got, want)
			}
		}
	}
}

func latticeFormulaHolds(formula Type, atoms []Type, valuation uint8) bool {
	switch typ := formula.(type) {
	case *NeverType:
		return false
	case *AnyType:
		return true
	case *UnionType:
		for _, member := range typ.Types {
			if latticeFormulaHolds(member, atoms, valuation) {
				return true
			}
		}
		return false
	case *IntersectionType:
		for _, member := range typ.Types {
			if !latticeFormulaHolds(member, atoms, valuation) {
				return false
			}
		}
		return true
	default:
		for index, atom := range atoms {
			if formula.Equals(atom) {
				return valuation&(1<<index) != 0
			}
		}
		panic("test lattice formula contains an unknown atom: " + formula.String())
	}
}
