package borrowchecker

import (
	"testing"

	"github.com/SCKelemen/oak/typechecker"
)

func TestFunctionReturningBorrowInRecordReportsEscape(t *testing.T) {
	for _, source := range []string{
		"Wrapped: type = struct { bytes: []u8 }\nleak: (buf: [16]u8): Wrapped { v: []u8 = buf[0:8]\nWrapped { bytes: v } }",
		"Wrapped: type = struct { bytes: [*]u8 }\nleak: (buf: [16]u8): Wrapped { v: [*]u8 = span(&buf)\nWrapped { bytes: v } }",
		"Inner: type = struct { bytes: []u8 }\nOuter: type = struct { inner: Inner }\nleak: (buf: [16]u8): Outer { v: []u8 = buf[0:8]\ni: Inner = Inner { bytes: v }\nOuter { inner: i } }",
	} {
		bc, program, tc := setupBorrowCheckerForTest(source)
		if program == nil {
			t.Fatalf("failed to parse: %s", source)
		}
		if errors := tc.Errors(); len(errors) != 0 {
			t.Fatalf("fixture must typecheck: %v", errors)
		}
		bc.CheckProgram(program, tc.Env())
		if got := countDiagnosticsWithCode(bc, string(CodeBorrowEscape)); got != 1 {
			t.Fatalf("got %d escape diagnostics, want 1: %#v", got, bc.Diagnostics())
		}
	}
}

func TestStructuralReturnBorrowClassification(t *testing.T) {
	byteType := &typechecker.PrimitiveType{Name: "u8"}
	view := &typechecker.ArrayType{IsSlice: true, Length: -1, ElementType: byteType}
	span := &typechecker.ArrayType{IsSpan: true, Length: -1, ElementType: byteType}
	recursive := &typechecker.RecordType{Fields: map[string]typechecker.Type{}}
	recursive.Fields["a_cycle"] = recursive
	recursive.Fields["z_bytes"] = view
	for _, fixture := range []struct {
		name string
		typ  typechecker.Type
		want string
	}{
		{"owned bytes", &typechecker.ArrayType{Length: 16, ElementType: byteType}, ""},
		{"array of views", &typechecker.ArrayType{Length: 2, ElementType: view}, "view"},
		{"array of spans", &typechecker.ArrayType{Length: 2, ElementType: span}, "span"},
		{"recursive record", recursive, "view"},
		{"union", &typechecker.UnionType{Types: []typechecker.Type{byteType, view}}, "view"},
		{"intersection", &typechecker.IntersectionType{Types: []typechecker.Type{byteType, span}}, "span"},
		{"string literal type", &typechecker.StringType{}, ""},
		{"function signature", &typechecker.FunctionType{ReturnType: view}, ""},
	} {
		t.Run(fixture.name, func(t *testing.T) {
			if got := returnedBorrowKind(fixture.typ, make(map[typechecker.Type]bool)); got != fixture.want {
				t.Fatalf("got %q, want %q", got, fixture.want)
			}
		})
	}
}
