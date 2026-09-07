package typechecker

import (
	"strings"
	"testing"
)

func TestExtensibleRecordAcceptsAdditionalFields(t *testing.T) {
	input := `Person: type = struct { name: string, age: u8 }
name: (p: { r | name: string }): string = p.name
main: (p: Person): string = name(p)
`
	tc := setupTypeChecker(input)
	tc.CheckProgram(parseProgram(input))
	if errs := tc.Errors(); len(errs) != 0 { t.Fatalf("unexpected errors: %v", errs) }
}

func TestExtensibleRecordRejectsMissingField(t *testing.T) {
	input := `Age: type = struct { age: u8 }
name: (p: { r | name: string }): string = p.name
main: (p: Age): string = name(p)
`
	tc := setupTypeChecker(input)
	tc.CheckProgram(parseProgram(input))
	if got := strings.Join(tc.Errors(), "\n"); !strings.Contains(got, "argument") {
		t.Fatalf("expected shape mismatch, got %v", tc.Errors())
	}
}

func TestFieldAccessorTypesDirectApplication(t *testing.T) {
	input := `Person: type = struct { name: string, age: u8 }
main: (p: Person): string = .name(p)
`
	tc := setupTypeChecker(input)
	tc.CheckProgram(parseProgram(input))
	if errs := tc.Errors(); len(errs) != 0 { t.Fatalf("unexpected errors: %v", errs) }
}

func TestFieldAccessorSpecializesAsFirstClassFunction(t *testing.T) {
	input := `Person: type = struct { name: i32, age: u8 }
fn apply(selector: (Person) -> i32, value: Person) -> i32 { selector(value) }
fn main(person: Person) -> i32 {
  getter: (Person) -> i32 = .name
  apply(.name, person) + getter(person)
}
`
	tc := setupTypeChecker(input)
	tc.CheckProgram(parseProgram(input))
	if errs := tc.Errors(); len(errs) != 0 {
		t.Fatalf("unexpected errors: %v", errs)
	}
}

func TestFieldAccessorWithoutContextIsRejected(t *testing.T) {
	input := `getter := .name`
	tc := setupTypeChecker(input)
	tc.CheckProgram(parseProgram(input))
	if got := strings.Join(tc.Errors(), "\n"); !strings.Contains(got, "explicit function type") {
		t.Fatalf("expected contextual accessor error, got %v", tc.Errors())
	}
}
