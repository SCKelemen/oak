package typechecker

import (
	"testing"
)

// TestLattice_Reflexivity tests that IsSubtype is reflexive: T ≤ T for all T
func TestLattice_Reflexivity(t *testing.T) {
	tests := []Type{
		&PrimitiveType{Name: "i32"},
		&PrimitiveType{Name: "u8"},
		&StringType{},
		&BoolType{},
		&UnitType{},
		&NeverType{},
		&AnyType{},
		&RecordType{Fields: map[string]Type{"x": &PrimitiveType{Name: "i32"}}},
		&ArrayType{ElementType: &PrimitiveType{Name: "u8"}, Length: 10, IsSlice: false, IsSpan: false},
		&UnionType{Types: []Type{&PrimitiveType{Name: "i32"}, &PrimitiveType{Name: "u8"}}},
		&IntersectionType{Types: []Type{&PrimitiveType{Name: "i32"}, &PrimitiveType{Name: "u8"}}},
	}

	for _, typ := range tests {
		t.Run(typ.String(), func(t *testing.T) {
			if !IsSubtype(typ, typ) {
				t.Errorf("IsSubtype(%s, %s) should be true (reflexivity)", typ, typ)
			}
		})
	}
}

// TestLattice_Transitivity tests that IsSubtype is transitive: if T1 ≤ T2 and T2 ≤ T3, then T1 ≤ T3
func TestLattice_Transitivity(t *testing.T) {
	tests := []struct {
		name string
		t1   Type
		t2   Type
		t3   Type
	}{
		{
			"never ≤ i32 ≤ any",
			&NeverType{},
			&PrimitiveType{Name: "i32"},
			&AnyType{},
		},
		{
			"never ≤ u8 ≤ any",
			&NeverType{},
			&PrimitiveType{Name: "u8"},
			&AnyType{},
		},
		{
			"never ≤ Unit ≤ any",
			&NeverType{},
			&UnitType{},
			&AnyType{},
		},
		{
			"never ≤ union ≤ any",
			&NeverType{},
			&UnionType{Types: []Type{&PrimitiveType{Name: "i32"}, &PrimitiveType{Name: "u8"}}},
			&AnyType{},
		},
		{
			"i32 ≤ union ≤ any",
			&PrimitiveType{Name: "i32"},
			&UnionType{Types: []Type{&PrimitiveType{Name: "i32"}, &PrimitiveType{Name: "u8"}}},
			&AnyType{},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if !IsSubtype(tt.t1, tt.t2) {
				t.Fatalf("Precondition failed: IsSubtype(%s, %s) should be true", tt.t1, tt.t2)
			}
			if !IsSubtype(tt.t2, tt.t3) {
				t.Fatalf("Precondition failed: IsSubtype(%s, %s) should be true", tt.t2, tt.t3)
			}
			if !IsSubtype(tt.t1, tt.t3) {
				t.Errorf("Transitivity failed: IsSubtype(%s, %s) should be true (since %s ≤ %s ≤ %s)",
					tt.t1, tt.t3, tt.t1, tt.t2, tt.t3)
			}
		})
	}
}

// TestLattice_NeverIsBottom tests that never is the bottom type: never ≤ T for all T
func TestLattice_NeverIsBottom(t *testing.T) {
	types := []Type{
		&PrimitiveType{Name: "i32"},
		&PrimitiveType{Name: "u8"},
		&StringType{},
		&BoolType{},
		&UnitType{},
		&AnyType{},
		&RecordType{Fields: map[string]Type{"x": &PrimitiveType{Name: "i32"}}},
		&ArrayType{ElementType: &PrimitiveType{Name: "u8"}, Length: 10, IsSlice: false, IsSpan: false},
		&UnionType{Types: []Type{&PrimitiveType{Name: "i32"}, &PrimitiveType{Name: "u8"}}},
		&IntersectionType{Types: []Type{&PrimitiveType{Name: "i32"}, &PrimitiveType{Name: "u8"}}},
	}

	never := &NeverType{}
	for _, typ := range types {
		t.Run(typ.String(), func(t *testing.T) {
			if !IsSubtype(never, typ) {
				t.Errorf("never should be ≤ %s (never is bottom)", typ)
			}
		})
	}
}

// TestLattice_AnyIsTop tests that any is the top type: T ≤ any for all T
func TestLattice_AnyIsTop(t *testing.T) {
	types := []Type{
		&PrimitiveType{Name: "i32"},
		&PrimitiveType{Name: "u8"},
		&StringType{},
		&BoolType{},
		&UnitType{},
		&NeverType{},
		&RecordType{Fields: map[string]Type{"x": &PrimitiveType{Name: "i32"}}},
		&ArrayType{ElementType: &PrimitiveType{Name: "u8"}, Length: 10, IsSlice: false, IsSpan: false},
		&UnionType{Types: []Type{&PrimitiveType{Name: "i32"}, &PrimitiveType{Name: "u8"}}},
		&IntersectionType{Types: []Type{&PrimitiveType{Name: "i32"}, &PrimitiveType{Name: "u8"}}},
	}

	anyType := &AnyType{}
	for _, typ := range types {
		t.Run(typ.String(), func(t *testing.T) {
			if !IsSubtype(typ, anyType) {
				t.Errorf("%s should be ≤ any (%s is top)", typ, anyType)
			}
		})
	}
}

// TestLattice_JoinIdentity tests join identity laws
func TestLattice_JoinIdentity(t *testing.T) {
	types := []Type{
		&PrimitiveType{Name: "i32"},
		&PrimitiveType{Name: "u8"},
		&StringType{},
		&BoolType{},
		&UnitType{},
		&NeverType{},
		&AnyType{},
	}

	for _, typ := range types {
		t.Run(typ.String(), func(t *testing.T) {
			// Join with itself should return itself (idempotency)
			joined := Join(typ, typ)
			if !joined.Equals(typ) {
				t.Errorf("Join(%s, %s) = %s, expected %s (idempotency)", typ, typ, joined, typ)
			}

			// Join with never should return the type (never is bottom)
			joinedWithNever := Join(typ, &NeverType{})
			if !joinedWithNever.Equals(typ) {
				t.Errorf("Join(%s, never) = %s, expected %s (never is bottom)", typ, joinedWithNever, typ)
			}

			// Join with any should return any (any is top)
			joinedWithAny := Join(typ, &AnyType{})
			if !joinedWithAny.Equals(&AnyType{}) {
				t.Errorf("Join(%s, any) = %s, expected any (any is top)", typ, joinedWithAny)
			}
		})
	}
}

// TestLattice_MeetIdentity tests meet identity laws
func TestLattice_MeetIdentity(t *testing.T) {
	types := []Type{
		&PrimitiveType{Name: "i32"},
		&PrimitiveType{Name: "u8"},
		&StringType{},
		&BoolType{},
		&UnitType{},
		&NeverType{},
		&AnyType{},
	}

	for _, typ := range types {
		t.Run(typ.String(), func(t *testing.T) {
			// Meet with itself should return itself (idempotency)
			met := Meet(typ, typ)
			if !met.Equals(typ) {
				t.Errorf("Meet(%s, %s) = %s, expected %s (idempotency)", typ, typ, met, typ)
			}

			// Meet with never should return never (never is bottom)
			metWithNever := Meet(typ, &NeverType{})
			if !metWithNever.Equals(&NeverType{}) {
				t.Errorf("Meet(%s, never) = %s, expected never (never is bottom)", typ, metWithNever)
			}

			// Meet with any should return the type (any is top)
			metWithAny := Meet(typ, &AnyType{})
			if !metWithAny.Equals(typ) {
				t.Errorf("Meet(%s, any) = %s, expected %s (any is top)", typ, metWithAny, typ)
			}
		})
	}
}

// TestLattice_JoinCommutativity tests that Join is commutative: Join(A, B) = Join(B, A)
func TestLattice_JoinCommutativity(t *testing.T) {
	tests := []struct {
		name string
		t1   Type
		t2   Type
	}{
		{"i32, u8", &PrimitiveType{Name: "i32"}, &PrimitiveType{Name: "u8"}},
		{"i32, string", &PrimitiveType{Name: "i32"}, &StringType{}},
		{"never, i32", &NeverType{}, &PrimitiveType{Name: "i32"}},
		{"i32, any", &PrimitiveType{Name: "i32"}, &AnyType{}},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			join1 := Join(tt.t1, tt.t2)
			join2 := Join(tt.t2, tt.t1)
			if !join1.Equals(join2) {
				t.Errorf("Join(%s, %s) = %s, but Join(%s, %s) = %s (should be equal)",
					tt.t1, tt.t2, join1, tt.t2, tt.t1, join2)
			}
		})
	}
}

// TestLattice_MeetCommutativity tests that Meet is commutative: Meet(A, B) = Meet(B, A)
func TestLattice_MeetCommutativity(t *testing.T) {
	tests := []struct {
		name string
		t1   Type
		t2   Type
	}{
		{"i32, u8", &PrimitiveType{Name: "i32"}, &PrimitiveType{Name: "u8"}},
		{"i32, string", &PrimitiveType{Name: "i32"}, &StringType{}},
		{"never, i32", &NeverType{}, &PrimitiveType{Name: "i32"}},
		{"i32, any", &PrimitiveType{Name: "i32"}, &AnyType{}},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			meet1 := Meet(tt.t1, tt.t2)
			meet2 := Meet(tt.t2, tt.t1)
			if !meet1.Equals(meet2) {
				t.Errorf("Meet(%s, %s) = %s, but Meet(%s, %s) = %s (should be equal)",
					tt.t1, tt.t2, meet1, tt.t2, tt.t1, meet2)
			}
		})
	}
}

// TestLattice_JoinAssociativity tests that Join is associative: Join(A, Join(B, C)) = Join(Join(A, B), C)
func TestLattice_JoinAssociativity(t *testing.T) {
	tests := []struct {
		name string
		t1   Type
		t2   Type
		t3   Type
	}{
		{"i32, u8, string", &PrimitiveType{Name: "i32"}, &PrimitiveType{Name: "u8"}, &StringType{}},
		{"never, i32, u8", &NeverType{}, &PrimitiveType{Name: "i32"}, &PrimitiveType{Name: "u8"}},
		{"i32, u8, any", &PrimitiveType{Name: "i32"}, &PrimitiveType{Name: "u8"}, &AnyType{}},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			joinLeft := Join(tt.t1, Join(tt.t2, tt.t3))
			joinRight := Join(Join(tt.t1, tt.t2), tt.t3)
			if !joinLeft.Equals(joinRight) {
				t.Errorf("Join(%s, Join(%s, %s)) = %s, but Join(Join(%s, %s), %s) = %s (should be equal)",
					tt.t1, tt.t2, tt.t3, joinLeft, tt.t1, tt.t2, tt.t3, joinRight)
			}
		})
	}
}

// TestLattice_MeetAssociativity tests that Meet is associative: Meet(A, Meet(B, C)) = Meet(Meet(A, B), C)
func TestLattice_MeetAssociativity(t *testing.T) {
	tests := []struct {
		name string
		t1   Type
		t2   Type
		t3   Type
	}{
		{"i32, u8, string", &PrimitiveType{Name: "i32"}, &PrimitiveType{Name: "u8"}, &StringType{}},
		{"never, i32, u8", &NeverType{}, &PrimitiveType{Name: "i32"}, &PrimitiveType{Name: "u8"}},
		{"i32, u8, any", &PrimitiveType{Name: "i32"}, &PrimitiveType{Name: "u8"}, &AnyType{}},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			meetLeft := Meet(tt.t1, Meet(tt.t2, tt.t3))
			meetRight := Meet(Meet(tt.t1, tt.t2), tt.t3)
			if !meetLeft.Equals(meetRight) {
				t.Errorf("Meet(%s, Meet(%s, %s)) = %s, but Meet(Meet(%s, %s), %s) = %s (should be equal)",
					tt.t1, tt.t2, tt.t3, meetLeft, tt.t1, tt.t2, tt.t3, meetRight)
			}
		})
	}
}

// TestLattice_JoinAbsorption tests absorption law: Join(A, Meet(A, B)) = A
func TestLattice_JoinAbsorption(t *testing.T) {
	tests := []struct {
		name string
		a    Type
		b    Type
	}{
		{"i32, u8", &PrimitiveType{Name: "i32"}, &PrimitiveType{Name: "u8"}},
		{"i32, string", &PrimitiveType{Name: "i32"}, &StringType{}},
		{"never, i32", &NeverType{}, &PrimitiveType{Name: "i32"}},
		{"i32, any", &PrimitiveType{Name: "i32"}, &AnyType{}},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			meetAB := Meet(tt.a, tt.b)
			joinAMeet := Join(tt.a, meetAB)
			if !joinAMeet.Equals(tt.a) {
				t.Errorf("Join(%s, Meet(%s, %s)) = Join(%s, %s) = %s, expected %s (absorption)",
					tt.a, tt.a, tt.b, tt.a, meetAB, joinAMeet, tt.a)
			}
		})
	}
}

// TestLattice_MeetAbsorption tests absorption law: Meet(A, Join(A, B)) = A
func TestLattice_MeetAbsorption(t *testing.T) {
	tests := []struct {
		name string
		a    Type
		b    Type
	}{
		{"i32, u8", &PrimitiveType{Name: "i32"}, &PrimitiveType{Name: "u8"}},
		{"i32, string", &PrimitiveType{Name: "i32"}, &StringType{}},
		{"never, i32", &NeverType{}, &PrimitiveType{Name: "i32"}},
		{"i32, any", &PrimitiveType{Name: "i32"}, &AnyType{}},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			joinAB := Join(tt.a, tt.b)
			meetAJoin := Meet(tt.a, joinAB)
			if !meetAJoin.Equals(tt.a) {
				t.Errorf("Meet(%s, Join(%s, %s)) = Meet(%s, %s) = %s, expected %s (absorption)",
					tt.a, tt.a, tt.b, tt.a, joinAB, meetAJoin, tt.a)
			}
		})
	}
}

// TestLattice_UnionSubtyping tests union subtyping: A ≤ A | B
func TestLattice_UnionSubtyping(t *testing.T) {
	tests := []struct {
		name string
		a    Type
		b    Type
	}{
		{"i32, u8", &PrimitiveType{Name: "i32"}, &PrimitiveType{Name: "u8"}},
		{"i32, string", &PrimitiveType{Name: "i32"}, &StringType{}},
		{"u8, bool", &PrimitiveType{Name: "u8"}, &BoolType{}},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			union := &UnionType{Types: []Type{tt.a, tt.b}}
			if !IsSubtype(tt.a, union) {
				t.Errorf("IsSubtype(%s, %s) should be true (A ≤ A | B)", tt.a, union)
			}
			if !IsSubtype(tt.b, union) {
				t.Errorf("IsSubtype(%s, %s) should be true (B ≤ A | B)", tt.b, union)
			}
		})
	}
}

// TestLattice_IntersectionSubtyping tests intersection subtyping: A & B ≤ A and A & B ≤ B
func TestLattice_IntersectionSubtyping(t *testing.T) {
	tests := []struct {
		name string
		a    Type
		b    Type
	}{
		{"i32, u8", &PrimitiveType{Name: "i32"}, &PrimitiveType{Name: "u8"}},
		{"i32, string", &PrimitiveType{Name: "i32"}, &StringType{}},
		{"u8, bool", &PrimitiveType{Name: "u8"}, &BoolType{}},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			intersection := &IntersectionType{Types: []Type{tt.a, tt.b}}
			if !IsSubtype(intersection, tt.a) {
				t.Errorf("IsSubtype(%s, %s) should be true (A & B ≤ A)", intersection, tt.a)
			}
			if !IsSubtype(intersection, tt.b) {
				t.Errorf("IsSubtype(%s, %s) should be true (A & B ≤ B)", intersection, tt.b)
			}
		})
	}
}
