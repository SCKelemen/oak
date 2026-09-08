package typechecker

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
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

func TestExtensibleRecordFunctionSpecializesForDistinctStructLayouts(t *testing.T) {
	input := `AB: type = struct { a: i32, b: u8 }
BA: type = struct { b: u8, a: i32 }
getA: (value: { r | a: i32 }): i32 = value.a
main: (): i32 {
  ab: AB = AB { a: 20, b: 1 }
  ba: BA = BA { b: 2, a: 22 }
  getA(ab) + getA(ba)
}
`
	program := parseProgram(input)
	tc := setupTypeChecker(input)
	tc.CheckProgram(program)
	if errs := tc.Errors(); len(errs) != 0 {
		t.Fatalf("unexpected errors: %v", errs)
	}
	seen := map[string]bool{}
	for _, statement := range program.Statements {
		if fn, ok := statement.(*ast.FunctionStatement); ok && fn.Name != nil {
			seen[fn.Name.Value] = true
			for _, parameter := range fn.Parameters {
				if record, open := parameter.Type.(*ast.RecordLiteral); open && record.Extension != nil {
					t.Fatalf("downstream function %s retained open-row ABI", fn.Name.Value)
				}
			}
		}
	}
	if !seen["getA_AB"] || !seen["getA_BA"] || seen["getA"] {
		t.Fatalf("specializations = %v, want getA_AB and getA_BA only", seen)
	}
}
