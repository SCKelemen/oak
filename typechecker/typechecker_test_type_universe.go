package typechecker

import (
	"testing"
)

// TestTypeEquality tests type equality according to the type universe spec
func TestTypeEquality(t *testing.T) {
	tests := []struct {
		name     string
		t1       Type
		t2       Type
		expected bool
	}{
		// Reflexivity: T = T
		{"u8 equals u8", &PrimitiveType{Name: "u8"}, &PrimitiveType{Name: "u8"}, true},
		{"i32 equals i32", &PrimitiveType{Name: "i32"}, &PrimitiveType{Name: "i32"}, true},
		{"string equals string", &StringType{}, &StringType{}, true},
		{"Bool equals Bool", &BoolType{}, &BoolType{}, true},
		{"Unit equals Unit", &UnitType{}, &UnitType{}, true},
		{"never equals never", &NeverType{}, &NeverType{}, true},
		{"any equals any", &AnyType{}, &AnyType{}, true},

		// Empty record {} equals Unit
		{"empty record equals Unit", &RecordType{Fields: map[string]Type{}}, &UnitType{}, true},
		{"Unit equals empty record", &UnitType{}, &RecordType{Fields: map[string]Type{}}, true},
		{"empty record equals empty record", &RecordType{Fields: map[string]Type{}}, &RecordType{Fields: map[string]Type{}}, true},

		// Non-empty records don't equal Unit
		{"non-empty record doesn't equal Unit", &RecordType{Fields: map[string]Type{"x": &PrimitiveType{Name: "u8"}}}, &UnitType{}, false},
		{"Unit doesn't equal non-empty record", &UnitType{}, &RecordType{Fields: map[string]Type{"x": &PrimitiveType{Name: "u8"}}}, false},

		// Different primitives don't equal
		{"u8 doesn't equal i32", &PrimitiveType{Name: "u8"}, &PrimitiveType{Name: "i32"}, false},
		{"u8 doesn't equal string", &PrimitiveType{Name: "u8"}, &StringType{}, false},

		// Record types equality
		{
			"identical records equal",
			&RecordType{Fields: map[string]Type{"x": &PrimitiveType{Name: "u8"}, "y": &PrimitiveType{Name: "u8"}}},
			&RecordType{Fields: map[string]Type{"x": &PrimitiveType{Name: "u8"}, "y": &PrimitiveType{Name: "u8"}}},
			true,
		},
		{
			"different field types don't equal",
			&RecordType{Fields: map[string]Type{"x": &PrimitiveType{Name: "u8"}}},
			&RecordType{Fields: map[string]Type{"x": &PrimitiveType{Name: "i32"}}},
			false,
		},
		{
			"different field names don't equal",
			&RecordType{Fields: map[string]Type{"x": &PrimitiveType{Name: "u8"}}},
			&RecordType{Fields: map[string]Type{"y": &PrimitiveType{Name: "u8"}}},
			false,
		},
		{
			"different field counts don't equal",
			&RecordType{Fields: map[string]Type{"x": &PrimitiveType{Name: "u8"}}},
			&RecordType{Fields: map[string]Type{"x": &PrimitiveType{Name: "u8"}, "y": &PrimitiveType{Name: "u8"}}},
			false,
		},

		// Union types equality
		{
			"identical unions equal",
			&UnionType{Types: []Type{&PrimitiveType{Name: "u8"}, &PrimitiveType{Name: "i32"}}},
			&UnionType{Types: []Type{&PrimitiveType{Name: "u8"}, &PrimitiveType{Name: "i32"}}},
			true,
		},
		{
			"unions with different order equal (order doesn't matter)",
			&UnionType{Types: []Type{&PrimitiveType{Name: "u8"}, &PrimitiveType{Name: "i32"}}},
			&UnionType{Types: []Type{&PrimitiveType{Name: "i32"}, &PrimitiveType{Name: "u8"}}},
			true,
		},
		{
			"unions with different types don't equal",
			&UnionType{Types: []Type{&PrimitiveType{Name: "u8"}}},
			&UnionType{Types: []Type{&PrimitiveType{Name: "i32"}}},
			false,
		},

		// Intersection types equality
		{
			"identical intersections equal",
			&IntersectionType{Types: []Type{&PrimitiveType{Name: "u8"}, &PrimitiveType{Name: "i32"}}},
			&IntersectionType{Types: []Type{&PrimitiveType{Name: "u8"}, &PrimitiveType{Name: "i32"}}},
			true,
		},
		{
			"intersections with different order equal (order doesn't matter)",
			&IntersectionType{Types: []Type{&PrimitiveType{Name: "u8"}, &PrimitiveType{Name: "i32"}}},
			&IntersectionType{Types: []Type{&PrimitiveType{Name: "i32"}, &PrimitiveType{Name: "u8"}}},
			true,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result := tt.t1.Equals(tt.t2)
			if result != tt.expected {
				t.Errorf("Type equality failed: %s.Equals(%s) = %v, expected %v",
					tt.t1.String(), tt.t2.String(), result, tt.expected)
			}
			// Test symmetry
			result2 := tt.t2.Equals(tt.t1)
			if result2 != tt.expected {
				t.Errorf("Type equality symmetry failed: %s.Equals(%s) = %v, expected %v",
					tt.t2.String(), tt.t1.String(), result2, tt.expected)
			}
		})
	}
}

// TestSubtyping tests the subtyping partial order from the type universe spec
func TestSubtyping(t *testing.T) {
	tests := []struct {
		name     string
		t1       Type
		t2       Type
		expected bool
		reason   string
	}{
		// Reflexivity: T ≤ T
		{"u8 ≤ u8", &PrimitiveType{Name: "u8"}, &PrimitiveType{Name: "u8"}, true, "reflexivity"},
		{"Unit ≤ Unit", &UnitType{}, &UnitType{}, true, "reflexivity"},
		{"never ≤ never", &NeverType{}, &NeverType{}, true, "reflexivity"},
		{"any ≤ any", &AnyType{}, &AnyType{}, true, "reflexivity"},

		// Bottom: never ≤ T for all T
		{"never ≤ u8", &NeverType{}, &PrimitiveType{Name: "u8"}, true, "never is bottom"},
		{"never ≤ i32", &NeverType{}, &PrimitiveType{Name: "i32"}, true, "never is bottom"},
		{"never ≤ string", &NeverType{}, &StringType{}, true, "never is bottom"},
		{"never ≤ Unit", &NeverType{}, &UnitType{}, true, "never is bottom"},
		{"never ≤ any", &NeverType{}, &AnyType{}, true, "never is bottom"},
		{"never ≤ record", &NeverType{}, &RecordType{Fields: map[string]Type{"x": &PrimitiveType{Name: "u8"}}}, true, "never is bottom"},

		// Top: T ≤ any for all T
		{"u8 ≤ any", &PrimitiveType{Name: "u8"}, &AnyType{}, true, "any is top"},
		{"i32 ≤ any", &PrimitiveType{Name: "i32"}, &AnyType{}, true, "any is top"},
		{"string ≤ any", &StringType{}, &AnyType{}, true, "any is top"},
		{"Unit ≤ any", &UnitType{}, &AnyType{}, true, "any is top"},
		{"never ≤ any", &NeverType{}, &AnyType{}, true, "any is top"},
		{"record ≤ any", &RecordType{Fields: map[string]Type{"x": &PrimitiveType{Name: "u8"}}}, &AnyType{}, true, "any is top"},

		// Union types: A ≤ A | B and B ≤ A | B
		{
			"u8 ≤ u8 | i32",
			&PrimitiveType{Name: "u8"},
			&UnionType{Types: []Type{&PrimitiveType{Name: "u8"}, &PrimitiveType{Name: "i32"}}},
			true,
			"union subtyping: A ≤ A | B",
		},
		{
			"i32 ≤ u8 | i32",
			&PrimitiveType{Name: "i32"},
			&UnionType{Types: []Type{&PrimitiveType{Name: "u8"}, &PrimitiveType{Name: "i32"}}},
			true,
			"union subtyping: B ≤ A | B",
		},
		{
			"u16 not ≤ u8 | i32",
			&PrimitiveType{Name: "u16"},
			&UnionType{Types: []Type{&PrimitiveType{Name: "u8"}, &PrimitiveType{Name: "i32"}}},
			false,
			"not a member of union",
		},

		// Intersection types: A & B ≤ A and A & B ≤ B
		{
			"u8 & i32 ≤ u8",
			&IntersectionType{Types: []Type{&PrimitiveType{Name: "u8"}, &PrimitiveType{Name: "i32"}}},
			&PrimitiveType{Name: "u8"},
			true,
			"intersection subtyping: A & B ≤ A",
		},
		{
			"u8 & i32 ≤ i32",
			&IntersectionType{Types: []Type{&PrimitiveType{Name: "u8"}, &PrimitiveType{Name: "i32"}}},
			&PrimitiveType{Name: "i32"},
			true,
			"intersection subtyping: A & B ≤ B",
		},
		{
			"u8 & i32 ≤ u16",
			&IntersectionType{Types: []Type{&PrimitiveType{Name: "u8"}, &PrimitiveType{Name: "i32"}}},
			&PrimitiveType{Name: "u16"},
			false,
			"intersection not subtype of unrelated type",
		},

		// Nominal types remain distinct (no structural subtyping)
		{"u8 not ≤ i32", &PrimitiveType{Name: "u8"}, &PrimitiveType{Name: "i32"}, false, "nominal types distinct"},
		{"i32 not ≤ u8", &PrimitiveType{Name: "i32"}, &PrimitiveType{Name: "u8"}, false, "nominal types distinct"},
		{"string not ≤ u8", &StringType{}, &PrimitiveType{Name: "u8"}, false, "nominal types distinct"},
		{
			"record1 not ≤ record2 (same shape, different names)",
			&RecordType{Fields: map[string]Type{"x": &PrimitiveType{Name: "u8"}}},
			&RecordType{Fields: map[string]Type{"x": &PrimitiveType{Name: "u8"}}},
			false,
			"nominal types: same shape but distinct",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result := IsSubtype(tt.t1, tt.t2)
			if result != tt.expected {
				t.Errorf("Subtyping failed: IsSubtype(%s, %s) = %v, expected %v (%s)",
					tt.t1.String(), tt.t2.String(), result, tt.expected, tt.reason)
			}
		})
	}
}

// TestSubtypingTransitivity tests that subtyping is transitive
func TestSubtypingTransitivity(t *testing.T) {
	tests := []struct {
		name     string
		t1       Type
		t2       Type
		t3       Type
		expected bool
	}{
		// never ≤ T ≤ any implies never ≤ any
		{"never ≤ u8 ≤ any", &NeverType{}, &PrimitiveType{Name: "u8"}, &AnyType{}, true},
		{"never ≤ Unit ≤ any", &NeverType{}, &UnitType{}, &AnyType{}, true},

		// A ≤ A | B ≤ any implies A ≤ any
		{
			"u8 ≤ u8|i32 ≤ any",
			&PrimitiveType{Name: "u8"},
			&UnionType{Types: []Type{&PrimitiveType{Name: "u8"}, &PrimitiveType{Name: "i32"}}},
			&AnyType{},
			true,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			// Test: if t1 ≤ t2 and t2 ≤ t3, then t1 ≤ t3
			if IsSubtype(tt.t1, tt.t2) && IsSubtype(tt.t2, tt.t3) {
				result := IsSubtype(tt.t1, tt.t3)
				if result != tt.expected {
					t.Errorf("Transitivity failed: IsSubtype(%s, %s) = %v, expected %v",
						tt.t1.String(), tt.t3.String(), result, tt.expected)
				}
			} else {
				t.Errorf("Prerequisites failed: IsSubtype(%s, %s) = %v, IsSubtype(%s, %s) = %v",
					tt.t1.String(), tt.t2.String(), IsSubtype(tt.t1, tt.t2),
					tt.t2.String(), tt.t3.String(), IsSubtype(tt.t2, tt.t3))
			}
		})
	}
}

// TestJoin tests the join (least upper bound) operation
func TestJoin(t *testing.T) {
	tests := []struct {
		name     string
		types    []Type
		expected Type
		reason   string
	}{
		// Empty join is bottom
		{"empty join", []Type{}, &NeverType{}, "empty join is bottom"},

		// Single type
		{"single u8", []Type{&PrimitiveType{Name: "u8"}}, &PrimitiveType{Name: "u8"}, "single type returns itself"},

		// Same types
		{"u8 join u8", []Type{&PrimitiveType{Name: "u8"}, &PrimitiveType{Name: "u8"}}, &PrimitiveType{Name: "u8"}, "same types"},

		// never doesn't affect join
		{"never join u8", []Type{&NeverType{}, &PrimitiveType{Name: "u8"}}, &PrimitiveType{Name: "u8"}, "never is bottom"},
		{"u8 join never", []Type{&PrimitiveType{Name: "u8"}, &NeverType{}}, &PrimitiveType{Name: "u8"}, "never is bottom"},

		// any dominates join
		{"any join u8", []Type{&AnyType{}, &PrimitiveType{Name: "u8"}}, &AnyType{}, "any is top"},
		{"u8 join any", []Type{&PrimitiveType{Name: "u8"}, &AnyType{}}, &AnyType{}, "any is top"},

		// Different types create union
		{
			"u8 join i32",
			[]Type{&PrimitiveType{Name: "u8"}, &PrimitiveType{Name: "i32"}},
			&UnionType{Types: []Type{&PrimitiveType{Name: "u8"}, &PrimitiveType{Name: "i32"}}},
			"incomparable types create union",
		},
		{
			"u8 join i32 join u16",
			[]Type{&PrimitiveType{Name: "u8"}, &PrimitiveType{Name: "i32"}, &PrimitiveType{Name: "u16"}},
			&UnionType{Types: []Type{&PrimitiveType{Name: "u8"}, &PrimitiveType{Name: "i32"}, &PrimitiveType{Name: "u16"}}},
			"multiple incomparable types create union",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result := Join(tt.types...)
			if !result.Equals(tt.expected) {
				t.Errorf("Join failed: Join(%v) = %s, expected %s (%s)",
					tt.types, result.String(), tt.expected.String(), tt.reason)
			}
		})
	}
}

// TestMeet tests the meet (greatest lower bound) operation
func TestMeet(t *testing.T) {
	tests := []struct {
		name     string
		types    []Type
		expected Type
		reason   string
	}{
		// Empty meet is top
		{"empty meet", []Type{}, &AnyType{}, "empty meet is top"},

		// Single type
		{"single u8", []Type{&PrimitiveType{Name: "u8"}}, &PrimitiveType{Name: "u8"}, "single type returns itself"},

		// Same types
		{"u8 meet u8", []Type{&PrimitiveType{Name: "u8"}, &PrimitiveType{Name: "u8"}}, &PrimitiveType{Name: "u8"}, "same types"},

		// never dominates meet
		{"never meet u8", []Type{&NeverType{}, &PrimitiveType{Name: "u8"}}, &NeverType{}, "never is bottom"},
		{"u8 meet never", []Type{&PrimitiveType{Name: "u8"}, &NeverType{}}, &NeverType{}, "never is bottom"},

		// any doesn't affect meet
		{"any meet u8", []Type{&AnyType{}, &PrimitiveType{Name: "u8"}}, &PrimitiveType{Name: "u8"}, "any is top"},
		{"u8 meet any", []Type{&PrimitiveType{Name: "u8"}, &AnyType{}}, &PrimitiveType{Name: "u8"}, "any is top"},

		// Different types create intersection
		{
			"u8 meet i32",
			[]Type{&PrimitiveType{Name: "u8"}, &PrimitiveType{Name: "i32"}},
			&IntersectionType{Types: []Type{&PrimitiveType{Name: "u8"}, &PrimitiveType{Name: "i32"}}},
			"incomparable types create intersection",
		},
		{
			"u8 meet i32 meet u16",
			[]Type{&PrimitiveType{Name: "u8"}, &PrimitiveType{Name: "i32"}, &PrimitiveType{Name: "u16"}},
			&IntersectionType{Types: []Type{&PrimitiveType{Name: "u8"}, &PrimitiveType{Name: "i32"}, &PrimitiveType{Name: "u16"}}},
			"multiple incomparable types create intersection",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result := Meet(tt.types...)
			if !result.Equals(tt.expected) {
				t.Errorf("Meet failed: Meet(%v) = %s, expected %s (%s)",
					tt.types, result.String(), tt.expected.String(), tt.reason)
			}
		})
	}
}

// TestUnionType tests union type creation and properties
func TestUnionType(t *testing.T) {
	u8 := &PrimitiveType{Name: "u8"}
	i32 := &PrimitiveType{Name: "i32"}
	stringType := &StringType{}

	union := &UnionType{Types: []Type{u8, i32}}
	union2 := &UnionType{Types: []Type{i32, u8}} // Different order

	// Test equality (order shouldn't matter)
	if !union.Equals(union2) {
		t.Error("Union types with same members in different order should be equal")
	}

	// Test string representation
	str := union.String()
	if str != "u8 | i32" && str != "i32 | u8" {
		t.Errorf("Union string representation incorrect: got %s, expected 'u8 | i32' or 'i32 | u8'", str)
	}

	// Test subtyping: u8 ≤ u8 | i32
	if !IsSubtype(u8, union) {
		t.Error("u8 should be a subtype of u8 | i32")
	}

	// Test subtyping: i32 ≤ u8 | i32
	if !IsSubtype(i32, union) {
		t.Error("i32 should be a subtype of u8 | i32")
	}

	// Test subtyping: string not ≤ u8 | i32
	if IsSubtype(stringType, union) {
		t.Error("string should not be a subtype of u8 | i32")
	}
}

// TestIntersectionType tests intersection type creation and properties
func TestIntersectionType(t *testing.T) {
	u8 := &PrimitiveType{Name: "u8"}
	i32 := &PrimitiveType{Name: "i32"}

	intersection := &IntersectionType{Types: []Type{u8, i32}}
	intersection2 := &IntersectionType{Types: []Type{i32, u8}} // Different order

	// Test equality (order shouldn't matter)
	if !intersection.Equals(intersection2) {
		t.Error("Intersection types with same members in different order should be equal")
	}

	// Test string representation
	str := intersection.String()
	if str != "u8 & i32" && str != "i32 & u8" {
		t.Errorf("Intersection string representation incorrect: got %s, expected 'u8 & i32' or 'i32 & u8'", str)
	}

	// Test subtyping: u8 & i32 ≤ u8
	if !IsSubtype(intersection, u8) {
		t.Error("u8 & i32 should be a subtype of u8")
	}

	// Test subtyping: u8 & i32 ≤ i32
	if !IsSubtype(intersection, i32) {
		t.Error("u8 & i32 should be a subtype of i32")
	}
}

// TestEmptyRecordCanonicalization tests that empty records are canonicalized to Unit
func TestEmptyRecordCanonicalization(t *testing.T) {
	emptyRecord := &RecordType{Fields: map[string]Type{}}
	unit := &UnitType{}

	// Empty record should equal Unit
	if !emptyRecord.Equals(unit) {
		t.Error("Empty record {} should equal Unit")
	}

	// Unit should equal empty record
	if !unit.Equals(emptyRecord) {
		t.Error("Unit should equal empty record {}")
	}

	// Both should be subtypes of any
	if !IsSubtype(emptyRecord, &AnyType{}) {
		t.Error("Empty record should be a subtype of any")
	}
	if !IsSubtype(unit, &AnyType{}) {
		t.Error("Unit should be a subtype of any")
	}

	// never should be subtype of both
	if !IsSubtype(&NeverType{}, emptyRecord) {
		t.Error("never should be a subtype of empty record")
	}
	if !IsSubtype(&NeverType{}, unit) {
		t.Error("never should be a subtype of Unit")
	}
}

// TestRecordTypeCanonicalization tests record type canonicalization
func TestRecordTypeCanonicalization(t *testing.T) {
	// Records with same fields in different order should be equal
	// (assuming canonicalization sorts fields)
	record1 := &RecordType{Fields: map[string]Type{
		"x": &PrimitiveType{Name: "u8"},
		"y": &PrimitiveType{Name: "u8"},
	}}
	record2 := &RecordType{Fields: map[string]Type{
		"y": &PrimitiveType{Name: "u8"},
		"x": &PrimitiveType{Name: "u8"},
	}}

	// They should be equal (same fields, same types)
	if !record1.Equals(record2) {
		t.Error("Records with same fields in different order should be equal")
	}

	// String representation should be canonical (sorted fields)
	str1 := record1.String()
	str2 := record2.String()
	if str1 != str2 {
		t.Errorf("Canonical string representations should match: %s vs %s", str1, str2)
	}
}

// TestTypeStringRepresentation tests that all types have proper string representations
func TestTypeStringRepresentation(t *testing.T) {
	tests := []struct {
		name     string
		typ      Type
		expected string
	}{
		{"u8", &PrimitiveType{Name: "u8"}, "u8"},
		{"i32", &PrimitiveType{Name: "i32"}, "i32"},
		{"string", &StringType{}, "string"},
		{"Bool", &BoolType{}, "Bool"},
		{"Unit", &UnitType{}, "()"},
		{"never", &NeverType{}, "never"},
		{"any", &AnyType{}, "any"},
		{
			"record",
			&RecordType{Fields: map[string]Type{"x": &PrimitiveType{Name: "u8"}}},
			"struct{ x: u8 }",
		},
		{
			"empty record",
			&RecordType{Fields: map[string]Type{}},
			"struct{}",
		},
		{
			"union",
			&UnionType{Types: []Type{&PrimitiveType{Name: "u8"}, &PrimitiveType{Name: "i32"}}},
			"u8 | i32",
		},
		{
			"intersection",
			&IntersectionType{Types: []Type{&PrimitiveType{Name: "u8"}, &PrimitiveType{Name: "i32"}}},
			"u8 & i32",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result := tt.typ.String()
			// For union/intersection, order might vary, so check contains
			if tt.name == "union" || tt.name == "intersection" {
				if result != "u8 | i32" && result != "i32 | u8" &&
					result != "u8 & i32" && result != "i32 & u8" {
					t.Errorf("String representation incorrect: got %s, expected union or intersection format", result)
				}
			} else if result != tt.expected {
				t.Errorf("String representation incorrect: got %s, expected %s", result, tt.expected)
			}
		})
	}
}
