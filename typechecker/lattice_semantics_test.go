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
