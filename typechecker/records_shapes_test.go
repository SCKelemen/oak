package typechecker

import (
	"strings"
	"testing"
)

// The record/struct axis (docs/spec/40-records.md §5): a semantic record
// type { a, b: u8 } is an order-free structural SHAPE; the struct keyword
// commits to an ordered concrete layout and, once named, to nominal
// identity. Both ordered structs over {a, b} satisfy the shape; neither
// substitutes for the other.
func TestStructsSatisfyRecordShapes(t *testing.T) {
	input := `u8_ab: type = { a, b: u8 }

AB: type = struct {
  a: u8
  b: u8
}

BA: type = struct {
  b: u8
  a: u8
}

sum: (v: u8_ab): u8 = v.a + v.b

both: (x: AB, y: BA): u8 = sum(x) + sum(y)
`
	tc := setupTypeChecker(input)
	program := parseProgram(input)
	tc.CheckProgram(program)
	if len(tc.Errors()) > 0 {
		t.Fatalf("both field orders must satisfy the shape, got: %v", tc.Errors())
	}
}

// Layout policy is not part of semantic shape identity. Natural, packed,
// aggregate-aligned, per-field-aligned, and reordered structs over the same
// members all satisfy the same record requirement.
func TestRecordShapeSatisfactionIgnoresConcreteLayoutPolicy(t *testing.T) {
	input := `
u8_ab: type = { a, b: u8 }

Natural: type = struct { a: u8, b: u8 }
Packed: type = struct(packed) { b: u8, a: u8 }
Aligned: type = struct(align: 16) { a: u8, b: u8 }
FieldAligned: type = struct {
  b(align: 16): u8
  a: u8
}

sum: (v: u8_ab): u8 = v.a + v.b

all: (n: Natural, p: Packed, a: Aligned, f: FieldAligned): u8 =
  sum(n) + sum(p) + sum(a) + sum(f)
`
	tc := setupTypeChecker(input)
	program := parseProgram(input)
	tc.CheckProgram(program)
	if len(tc.Errors()) > 0 {
		t.Fatalf("layout policy must not affect record-shape satisfaction: %v", tc.Errors())
	}
}

// Named structs stay nominal islands even when a shape would match:
// ordered representation is identity, and BA is not AB.
func TestOrderedStructsRemainNominal(t *testing.T) {
	input := `AB: type = struct {
  a: u8
  b: u8
}

BA: type = struct {
  b: u8
  a: u8
}

takeAB: (v: AB): u8 = v.a

f: (y: BA): u8 = takeAB(y)
`
	tc := setupTypeChecker(input)
	program := parseProgram(input)
	tc.CheckProgram(program)
	if len(tc.Errors()) == 0 {
		t.Fatal("BA where AB is expected must be rejected (nominal structs)")
	}
	joined := strings.Join(tc.Errors(), "\n")
	if !strings.Contains(joined, "AB") || !strings.Contains(joined, "BA") {
		t.Fatalf("rejection should name both nominal types, got: %v", tc.Errors())
	}
}

// Grouped field names declare each name at the shared type, in written
// order — { a, b: u8 } is a and b, both u8.
func TestGroupedFieldNames(t *testing.T) {
	input := `Pair: type = struct { a, b: u8 }
`
	tc := setupTypeChecker(input)
	program := parseProgram(input)
	tc.CheckProgram(program)
	if len(tc.Errors()) > 0 {
		t.Fatal(tc.Errors())
	}
	declared, ok := tc.Env().GetType("Pair")
	if !ok {
		t.Fatal("Pair not registered")
	}
	record, ok := declared.(*RecordType)
	if !ok {
		t.Fatalf("expected RecordType, got %T", declared)
	}
	if len(record.Order) != 2 || record.Order[0] != "a" || record.Order[1] != "b" {
		t.Fatalf("declaration order = %v, want [a b]", record.Order)
	}
	if !record.Struct {
		t.Fatal("struct declaration must be representation-committed")
	}
}
