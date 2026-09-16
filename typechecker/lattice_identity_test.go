package typechecker

import (
	"testing"

	"github.com/SCKelemen/oak/semir"
)

func TestLatticeAtomIdentityIsAnEquivalence(t *testing.T) {
	tv := &TypeVar{Name: "T", ID: 1}
	u8 := &PrimitiveType{Name: "u8"}
	shape := map[string]Type{"x": u8}
	fn := &FunctionType{Parameters: []Type{u8}, ReturnType: &BoolType{}}
	span := &ArrayType{ElementType: u8, Length: -1, IsSpan: true}
	option := &GenericType{Name: "Option", TypeArgs: []Type{u8}}
	foreign := &CFnType{Parameters: []Type{&CType{Name: "UInt8"}}, ReturnType: &CType{Name: "UInt8"}}
	atoms := []Type{
		u8, &PrimitiveType{Name: "u8"}, &PrimitiveType{Name: "byte"},
		&PrimitiveType{Name: "u8", Refinement: "Small"},
		&StringType{}, &StringType{Encoding: "Utf8"}, &StringType{Encoding: "Ascii"},
		&BoolType{}, &UnitType{}, &NeverType{}, &AnyType{}, &ADTType{Name: "Choice"},
		&NarrowedADTVariantType{ADTName: "Choice", VariantName: "Left"},
		&NarrowedADTVariantType{ADTName: "Choice", VariantName: "Left"},
		&NarrowedADTVariantType{ADTName: "Choice", VariantName: "Right"},
		&RecordType{Fields: shape}, &RecordType{Fields: map[string]Type{"x": &PrimitiveType{Name: "byte"}}},
		&RecordType{Name: "Shape", Fields: shape},
		&RecordType{Name: "StoredA", Struct: true, Fields: shape},
		&RecordType{Name: "StoredA", Struct: true, Fields: map[string]Type{"different": &BoolType{}}},
		&RecordType{Name: "StoredB", Struct: true, Fields: shape},
		&InterfaceType{Name: "Readable"},
		&UnionType{Types: []Type{u8, &BoolType{}}},
		&UnionType{Types: []Type{&BoolType{}, u8}},
		&IntersectionType{Types: []Type{u8, &BoolType{}}},
		&FieldAccessorType{Field: "x"},
		fn, &FunctionType{Parameters: []Type{&PrimitiveType{Name: "byte"}}, ReturnType: &BoolType{}},
		&FunctionType{Parameters: []Type{u8}, ReturnType: &BoolType{}, Variadic: true},
		span, &ArrayType{ElementType: &PrimitiveType{Name: "byte"}, Length: -1, IsSpan: true},
		&ArrayType{ElementType: u8, Length: -1, IsSpan: true, Align: 64},
		option, &GenericType{Name: "Option", TypeArgs: []Type{&PrimitiveType{Name: "byte"}}},
		tv, &TypeVar{Name: "T", ID: 1},
		&constraintSetType{Requirements: []string{"Readable", "Writable"}},
		&CType{Name: "UInt8"}, &SimdType{Name: "U8x16"},
		&MmioRegisterType{Width: semir.Mmio32, Access: semir.MmioReadOnly},
		&BufferType{Element: u8}, &BufferType{Element: u8, Custody: HostCustody},
		&AtomicType{Element: u8}, &AtomicType{Element: &PrimitiveType{Name: "byte"}},
		foreign, &CFnType{Parameters: []Type{&CType{Name: "UInt8"}}, ReturnType: &CType{Name: "UInt8"}},
		&ConstIntType{Value: 4},
	}

	for i, a := range atoms {
		if !latticeAtomIdentical(a, a) {
			t.Fatalf("atom %d (%T %s) is not identical to itself", i, a, a)
		}
		for j, b := range atoms {
			ab := latticeAtomIdentical(a, b)
			if ab != latticeAtomIdentical(b, a) {
				t.Fatalf("atom identity is asymmetric for %d (%s) and %d (%s)", i, a, j, b)
			}
			for k, c := range atoms {
				if ab && latticeAtomIdentical(b, c) && !latticeAtomIdentical(a, c) {
					t.Fatalf("atom identity is not transitive for %d (%s), %d (%s), %d (%s)", i, a, j, b, k, c)
				}
			}
		}
	}

	for _, a := range atoms {
		for _, b := range atoms {
			for _, c := range atoms {
				if IsSubtype(a, b) && IsSubtype(b, c) && !IsSubtype(a, c) {
					t.Fatalf("IsSubtype is not transitive for %s, %s, %s", a, b, c)
				}
			}
		}
	}
}

func TestLatticeAtomIdentityDoesNotUseADTCompatibility(t *testing.T) {
	parent := &ADTType{Name: "Choice"}
	left := &NarrowedADTVariantType{ADTName: "Choice", VariantName: "Left"}
	right := &NarrowedADTVariantType{ADTName: "Choice", VariantName: "Right"}

	if !left.Equals(parent) || !parent.Equals(right) {
		t.Fatal("regression setup no longer exercises the broader ADT compatibility relation")
	}
	if IsSubtype(left, parent) || IsSubtype(parent, right) || IsSubtype(left, right) {
		t.Fatal("narrowed cases and their parent must be distinct opaque lattice atoms")
	}
	tc := setupTypeChecker("")
	if !tc.isAssignable(left, parent) || tc.isAssignable(parent, left) {
		t.Fatal("case-to-parent compatibility must remain explicit and directional in assignability")
	}
	joinResult := Join(left, parent)
	joined, ok := joinResult.(*UnionType)
	if !ok || len(joined.Types) != 2 || !IsSubtype(left, joined) || !IsSubtype(parent, joined) {
		t.Fatalf("compatible-but-distinct ADT atoms must form their semantic join, got %T %v", joinResult, joinResult)
	}
	meetResult := Meet(left, parent)
	met, ok := meetResult.(*IntersectionType)
	if !ok || len(met.Types) != 2 || !IsSubtype(met, left) || !IsSubtype(met, parent) {
		t.Fatalf("compatible-but-distinct ADT atoms must form their semantic meet, got %T %v", meetResult, meetResult)
	}
}

func TestLatticeAtomIdentityDoesNotUseRecordShapeCompatibility(t *testing.T) {
	u8 := &PrimitiveType{Name: "u8"}
	fields := map[string]Type{"x": u8}
	shape := &RecordType{Fields: fields}
	storedA := &RecordType{Name: "StoredA", Struct: true, Fields: fields}
	storedB := &RecordType{Name: "StoredB", Struct: true, Fields: fields}

	if !storedA.Equals(shape) || !shape.Equals(storedB) {
		t.Fatal("regression setup no longer exercises the broader record-shape compatibility relation")
	}
	if IsSubtype(storedA, shape) || IsSubtype(shape, storedB) || IsSubtype(storedA, storedB) {
		t.Fatal("nominal structs and their shared shape must be distinct opaque lattice atoms")
	}
	tc := setupTypeChecker("")
	if !tc.isAssignable(storedA, shape) || tc.isAssignable(shape, storedA) {
		t.Fatal("struct-to-shape compatibility must remain explicit and directional in assignability")
	}
	joinResult := Join(storedA, shape)
	joined, ok := joinResult.(*UnionType)
	if !ok || len(joined.Types) != 2 || !IsSubtype(storedA, joined) || !IsSubtype(shape, joined) {
		t.Fatalf("a nominal struct and semantic shape must form their semantic join, got %T %v", joinResult, joinResult)
	}
	meetResult := Meet(storedA, shape)
	met, ok := meetResult.(*IntersectionType)
	if !ok || len(met.Types) != 2 || !IsSubtype(met, storedA) || !IsSubtype(met, shape) {
		t.Fatalf("a nominal struct and semantic shape must form their semantic meet, got %T %v", meetResult, meetResult)
	}
}

func TestAlignmentStaysOutsideTheOpaqueAtomLattice(t *testing.T) {
	element := &PrimitiveType{Name: "u8"}
	plain := &ArrayType{ElementType: element, Length: -1, IsSpan: true}
	aligned := &ArrayType{ElementType: element, Length: -1, IsSpan: true, Align: 64}

	for _, operands := range [][2]Type{{plain, aligned}, {aligned, plain}} {
		joinResult := Join(operands[0], operands[1])
		joined, ok := joinResult.(*UnionType)
		if !ok || !IsSubtype(plain, joined) || !IsSubtype(aligned, joined) {
			t.Fatalf("opaque alignment atoms must form a true lattice join, got %T %v", joinResult, joinResult)
		}
		meetResult := Meet(operands[0], operands[1])
		met, ok := meetResult.(*IntersectionType)
		if !ok || !IsSubtype(met, plain) || !IsSubtype(met, aligned) {
			t.Fatalf("opaque alignment atoms must form a true lattice meet, got %T %v", meetResult, meetResult)
		}
		flow, ok := joinValueFlowTypes(operands[0], operands[1]).(*ArrayType)
		if !ok || flow.Align != 0 {
			t.Fatalf("value-flow alignment join must keep the weakest fact, got %T %v", flow, flow)
		}
	}
}

func TestRepresentationPreservingAssignabilityIsDirectionalAndNested(t *testing.T) {
	tc := setupTypeChecker("")
	parent := &ADTType{Name: "Choice"}
	left := &NarrowedADTVariantType{ADTName: "Choice", VariantName: "Left"}
	plain := &ArrayType{ElementType: &PrimitiveType{Name: "u8"}, Length: -1, IsSpan: true}
	aligned := &ArrayType{ElementType: &PrimitiveType{Name: "u8"}, Length: -1, IsSpan: true, Align: 64}

	tests := []struct {
		name          string
		value, target Type
		want          bool
	}{
		{name: "case to parent", value: left, target: parent, want: true},
		{name: "parent to case", value: parent, target: left, want: false},
		{name: "aligned to plain", value: aligned, target: plain, want: true},
		{name: "plain to aligned", value: plain, target: aligned, want: false},
		{name: "record field parent to case", value: &RecordType{Fields: map[string]Type{"v": parent}}, target: &RecordType{Fields: map[string]Type{"v": left}}, want: false},
		{name: "record field weak to strong alignment", value: &RecordType{Fields: map[string]Type{"v": plain}}, target: &RecordType{Fields: map[string]Type{"v": aligned}}, want: false},
		{name: "span element compatibility is invariant", value: &ArrayType{ElementType: parent, Length: -1, IsSpan: true}, target: &ArrayType{ElementType: left, Length: -1, IsSpan: true}, want: false},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			if got := tc.isAssignable(test.value, test.target); got != test.want {
				t.Fatalf("isAssignable(%s, %s) = %v, want %v", test.value, test.target, got, test.want)
			}
		})
	}
}

func TestFunctionAlignmentAssignabilityKeepsVarianceAndExactShape(t *testing.T) {
	tc := setupTypeChecker("")
	u8 := &PrimitiveType{Name: "u8"}
	plain := &ArrayType{ElementType: u8, Length: -1, IsSpan: true}
	aligned := &ArrayType{ElementType: u8, Length: -1, IsSpan: true, Align: 64}
	returns := &BoolType{}
	takesPlain := &FunctionType{Parameters: []Type{plain}, ReturnType: returns}
	takesAligned := &FunctionType{Parameters: []Type{aligned}, ReturnType: returns}
	returnsPlain := &FunctionType{Parameters: []Type{&BoolType{}}, ReturnType: plain}
	returnsAligned := &FunctionType{Parameters: []Type{&BoolType{}}, ReturnType: aligned}

	if !tc.isAssignable(takesPlain, takesAligned) || tc.isAssignable(takesAligned, takesPlain) {
		t.Fatal("function parameter alignment must be contravariant")
	}
	if !tc.isAssignable(returnsAligned, returnsPlain) || tc.isAssignable(returnsPlain, returnsAligned) {
		t.Fatal("function result alignment must be covariant")
	}
	variadic := &FunctionType{Parameters: []Type{plain}, ReturnType: returns, Variadic: true}
	if tc.isAssignable(takesPlain, variadic) || tc.isAssignable(variadic, takesPlain) {
		t.Fatal("alignment compatibility must not erase variadic function identity")
	}
}
