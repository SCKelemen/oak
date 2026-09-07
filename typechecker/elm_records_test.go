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
