package typechecker

import "testing"

func TestAtomicTypeEquality(t *testing.T) {
	a, err := NewAtomicType(&PrimitiveType{Name: "u32"})
	if err != nil {
		t.Fatal(err)
	}
	b, err := NewAtomicType(&PrimitiveType{Name: "u32"})
	if err != nil {
		t.Fatal(err)
	}
	c, err := NewAtomicType(&PrimitiveType{Name: "u64"})
	if err != nil {
		t.Fatal(err)
	}
	if !a.Equals(b) {
		t.Fatal("equal atomic carriers should produce equal atomic types")
	}
	if a.Equals(c) {
		t.Fatal("different atomic carriers should not compare equal")
	}
	if a.String() != "Atomic[u32]" {
		t.Fatalf("unexpected atomic type string: %s", a.String())
	}
}

func TestAtomicCarrierIsFixedWidthOnly(t *testing.T) {
	for _, name := range []string{"u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64", "byte", "rune"} {
		if !IsAtomicCarrier(&PrimitiveType{Name: name}) {
			t.Fatalf("expected %s to be an atomic carrier", name)
		}
	}
	for _, name := range []string{"int", "uint", "ptr", "uptr"} {
		if IsAtomicCarrier(&PrimitiveType{Name: name}) {
			t.Fatalf("expected %s to be rejected as an atomic carrier", name)
		}
	}
	if IsAtomicCarrier(&BoolType{}) {
		t.Fatal("Bool must not be an atomic carrier in v1")
	}
}

func TestNewAtomicTypeRejectsUnsupportedCarrier(t *testing.T) {
	if _, err := NewAtomicType(&PrimitiveType{Name: "ptr"}); err == nil {
		t.Fatal("expected pointer carrier rejection")
	}
	if _, err := NewAtomicType(nil); err == nil {
		t.Fatal("expected nil carrier rejection")
	}
}
