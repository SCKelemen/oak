package typechecker

import (
	"strings"
	"testing"
)

// Typed record construction and field access (docs/spec/40-records.md):
// a literal against a declared type covers the fields exactly, field access
// types from the declaration, and the declared type keeps its nominal name
// and declaration order for the backend.
func TestRecordConstructionRules(t *testing.T) {
	point := "Point: type = struct {\n  x: i32\n  y: i32\n}\n\n"
	tests := []struct {
		name       string
		input      string
		hasError   bool
		wantInText string
	}{
		{
			"exact construction and field access",
			point + "shift: (p: Point, dx: i32): Point = Point { x: p.x + dx, y: p.y }",
			false, "",
		},
		{
			"missing field",
			point + "f: (): Point = Point { x: 1 }",
			true, "missing field y",
		},
		{
			"unknown field",
			point + "f: (): Point = Point { x: 1, y: 2, z: 3 }",
			true, "no field z",
		},
		{
			"field type mismatch",
			point + "f: (v: u64): Point = Point { x: v, y: 2 }",
			true, "field x expects i32",
		},
		{
			"field access has the declared type",
			point + "f: (p: Point): u8 = p.x",
			true, "", // i32 result vs u8 return
		},
		{
			"unknown field access",
			point + "f: (p: Point): i32 = p.z",
			true, "field z not found",
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			tc := setupTypeChecker(tt.input)
			program := parseProgram(tt.input)
			tc.CheckProgram(program)
			hasError := len(tc.Errors()) > 0
			if hasError != tt.hasError {
				t.Fatalf("expected error=%v, got %v", tt.hasError, tc.Errors())
			}
			if tt.wantInText != "" && !strings.Contains(strings.Join(tc.Errors(), "\n"), tt.wantInText) {
				t.Fatalf("errors %v do not mention %q", tc.Errors(), tt.wantInText)
			}
		})
	}
}

// The declared type carries nominal name and declaration order — the
// backend's struct emission and the proven layout depend on both.
func TestRecordTypeKeepsNameAndOrder(t *testing.T) {
	input := "Point: type = struct {\n  y: i32\n  x: i32\n}\n"
	tc := setupTypeChecker(input)
	program := parseProgram(input)
	tc.CheckProgram(program)
	if len(tc.Errors()) > 0 {
		t.Fatal(tc.Errors())
	}
	declared, ok := tc.Env().GetType("Point")
	if !ok {
		t.Fatal("Point not registered")
	}
	record, ok := declared.(*RecordType)
	if !ok {
		t.Fatalf("expected RecordType, got %T", declared)
	}
	if record.Name != "Point" {
		t.Fatalf("nominal name = %q, want Point", record.Name)
	}
	if len(record.Order) != 2 || record.Order[0] != "y" || record.Order[1] != "x" {
		t.Fatalf("declaration order = %v, want [y x]", record.Order)
	}
}
