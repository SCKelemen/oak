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

// A successful unification is inference evidence, not permission for the
// symmetric Type.Equals compatibility to reverse a structural shape flow.
func TestSemanticShapeCannotFlowIntoNominalStructAfterUnification(t *testing.T) {
	input := `Shape: type = { x: u8 }
Stored: type = struct { x: u8 }

take: (v: Stored): u8 = v.x

bad_call: (v: Shape): u8 = take(v)
bad_binding: (v: Shape): u8 {
  stored: Stored = v
  stored.x
}
`
	tc := setupTypeChecker(input)
	tc.CheckProgram(parseProgram(input))
	joined := strings.Join(tc.Errors(), "\n")
	if !strings.Contains(joined, "argument 1: expected Stored, got") ||
		!strings.Contains(joined, "variable stored: expected type Stored") {
		t.Fatalf("reverse shape flow escaped a successful unification: %v", tc.Errors())
	}
}

// Contextual record-literal checking is value flow, so it must use the same
// directional rule as calls and bindings rather than symmetric shape
// compatibility for each field.
func TestSemanticShapeCannotInitializeNominalRecordField(t *testing.T) {
	input := `Shape: type = { x: u8 }
Stored: type = struct { x: u8 }
Carrier: type = struct { item: Stored }

good: (v: Stored): Carrier = Carrier { item: v }
bad: (v: Shape): Carrier = Carrier { item: v }
`
	tc := setupTypeChecker(input)
	tc.CheckProgram(parseProgram(input))
	joined := strings.Join(tc.Errors(), "\n")
	if !strings.Contains(joined, "record literal: field item expects Stored") {
		t.Fatalf("shape value initialized a nominal record field: %v", tc.Errors())
	}
}

// Untyped array inference has no target to authorize directional shape flow.
// It therefore requires atom identity (apart from numeric promotion), and its
// result must not depend on which compatible-looking type appears first.
func TestArrayInferenceRejectsNominalShapeMixturesInBothOrders(t *testing.T) {
	for _, elements := range []string{"stored, shape", "shape, stored"} {
		input := `Shape: type = { x: u8 }
Stored: type = struct { x: u8 }

mixed: (stored: Stored, shape: Shape): () {
  values := [` + elements + `]
}
`
		tc := setupTypeChecker(input)
		tc.CheckProgram(parseProgram(input))
		joined := strings.Join(tc.Errors(), "\n")
		if !strings.Contains(joined, "array element") {
			t.Fatalf("array inference accepted nominal/shape mixture %q: %v", elements, tc.Errors())
		}
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
