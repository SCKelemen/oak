package typechecker

import (
	"strings"
	"testing"
)

func checkGenericShapeSource(t *testing.T, input string) []string {
	t.Helper()
	tc := setupTypeChecker(input)
	program := parseProgram(input)
	tc.CheckProgram(program)
	return tc.Errors()
}

func TestGenericRecordShapeAcceptsConcreteStructWithExtraFields(t *testing.T) {
	input := `
Position: type = { x: i32, y: i32 }
Point3: type = struct { x: i32, y: i32, z: i32 }
fn [T: Position] sum_xy(p: T) -> i32 { p.x + p.y }
p: Point3 = Point3 { x: 1, y: 2, z: 3 }
result: i32 = sum_xy(p)
`
	if errs := checkGenericShapeSource(t, input); len(errs) != 0 {
		t.Fatalf("unexpected errors: %v", errs)
	}
}

func TestGenericRecordShapeAcceptsSemanticRecordCandidate(t *testing.T) {
	input := `
Position: type = { x: i32, y: i32 }
NamedPoint: type = { name: string, y: i32, x: i32 }
fn [T: Position] sum_xy(p: T) -> i32 { p.x + p.y }
p: NamedPoint = NamedPoint { name: "oak", y: 2, x: 1 }
result: i32 = sum_xy(p)
`
	if errs := checkGenericShapeSource(t, input); len(errs) != 0 {
		t.Fatalf("unexpected errors: %v", errs)
	}
}

func TestGenericRecordShapeRejectsMissingField(t *testing.T) {
	input := `
Position: type = { x: i32, y: i32 }
Point1: type = struct { x: i32 }
fn [T: Position] sum_xy(p: T) -> i32 { p.x + p.y }
p: Point1 = Point1 { x: 1 }
result: i32 = sum_xy(p)
`
	errs := checkGenericShapeSource(t, input)
	if len(errs) == 0 {
		t.Fatal("expected record-shape constraint error")
	}
	if !strings.Contains(strings.Join(errs, "\n"), "does not satisfy constraint") {
		t.Fatalf("unexpected errors: %v", errs)
	}
}

func TestGenericRecordShapeRejectsWrongFieldType(t *testing.T) {
	input := `
Position: type = { x: i32, y: i32 }
BadPoint: type = struct { x: i32, y: u32 }
fn [T: Position] sum_xy(p: T) -> i32 { p.x + p.y }
p: BadPoint = BadPoint { x: 1, y: u32(2) }
result: i32 = sum_xy(p)
`
	errs := checkGenericShapeSource(t, input)
	if len(errs) == 0 {
		t.Fatal("expected record-shape constraint error")
	}
	if !strings.Contains(strings.Join(errs, "\n"), "does not satisfy constraint") {
		t.Fatalf("unexpected errors: %v", errs)
	}
}

func TestGenericBodyCannotUseFieldNotGuaranteedByConstraint(t *testing.T) {
	input := `
Position: type = { x: i32, y: i32 }
fn [T: Position] read_z(p: T) -> i32 { p.z }
`
	errs := checkGenericShapeSource(t, input)
	if len(errs) == 0 {
		t.Fatal("expected error for field not guaranteed by record-shape constraint")
	}
	if !strings.Contains(strings.Join(errs, "\n"), "not guaranteed by constraints") {
		t.Fatalf("unexpected errors: %v", errs)
	}
}

func TestGenericRecordShapeIntersectionGuaranteesFields(t *testing.T) {
	input := `
Position: type = { x: i32, y: i32 }
Tagged: type = { tag: u32 }
Point: type = struct { tag: u32, z: i32, y: i32, x: i32 }
fn [T: Position & Tagged] tag_of(p: T) -> u32 { p.tag }
p: Point = Point { tag: u32(7), z: 9, y: 2, x: 1 }
tag: u32 = tag_of(p)
`
	if errs := checkGenericShapeSource(t, input); len(errs) != 0 {
		t.Fatalf("unexpected errors: %v", errs)
	}
}

func TestGenericRecordShapeReturnTypeUsesInferredConcreteType(t *testing.T) {
	input := `
Position: type = { x: i32, y: i32 }
Point3: type = struct { x: i32, y: i32, z: i32 }
fn [T: Position] keep(p: T) -> T { p }
p: Point3 = Point3 { x: 1, y: 2, z: 3 }
q: Point3 = keep(p)
`
	if errs := checkGenericShapeSource(t, input); len(errs) != 0 {
		t.Fatalf("unexpected errors: %v", errs)
	}
}
