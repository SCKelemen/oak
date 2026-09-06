package typechecker

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

func findDiagnosticByCode(tc *TypeChecker, code string) *diagnostic.Diagnostic {
	for _, d := range tc.Diagnostics() {
		if d.Code == code {
			return d
		}
	}
	return nil
}

func TestGenericShapeFailureExplainsInferredTypeAndMissingField(t *testing.T) {
	input := `
Position: type = { x: i32, y: i32 }
Point1: type = struct { x: i32 }
fn [T: Position] sum_xy(p: T) -> i32 { p.x + p.y }
p: Point1 = Point1 { x: 1 }
result: i32 = sum_xy(p)
`
	tc := setupTypeChecker(input)
	program := parseProgram(input)
	tc.CheckProgram(program)

	d := findDiagnosticByCode(tc, CodeConstraintUnsatisfied)
	if d == nil {
		t.Fatalf("expected %s, got diagnostics: %#v", CodeConstraintUnsatisfied, tc.Diagnostics())
	}
	if d.Category != diagnostic.CategoryType {
		t.Fatalf("expected type category, got %q", d.Category)
	}
	if !strings.Contains(d.Title, "Point1") || !strings.Contains(d.Title, "T: Position") {
		t.Fatalf("title should identify inferred type and contract, got %q", d.Title)
	}
	if err := d.Validate(); err != nil {
		t.Fatalf("diagnostic should be structurally well formed: %v", err)
	}

	var sawInference, sawMissingField, sawHelp bool
	for _, advice := range d.Advice {
		switch advice.Kind {
		case diagnostic.AdviceNote:
			sawInference = sawInference || strings.Contains(advice.Message, "T = Point1")
			sawMissingField = sawMissingField || strings.Contains(advice.Message, "y: i32")
		case diagnostic.AdviceHelp:
			sawHelp = true
		}
	}
	if !sawInference || !sawMissingField || !sawHelp {
		t.Fatalf("expected inference, missing-field, and help context, got %#v", d.Advice)
	}
}

func TestUnknownGenericRequirementHasStableDiagnosticCode(t *testing.T) {
	input := `
fn [T: MissingRequirement] identity(x: T) -> T { x }
`
	tc := setupTypeChecker(input)
	program := parseProgram(input)
	tc.CheckProgram(program)

	d := findDiagnosticByCode(tc, CodeConstraintRequirementMissing)
	if d == nil {
		t.Fatalf("expected %s, got diagnostics: %#v", CodeConstraintRequirementMissing, tc.Diagnostics())
	}
	if !strings.Contains(d.Title, "MissingRequirement") {
		t.Fatalf("expected missing requirement in title, got %q", d.Title)
	}
	if len(d.Advice) == 0 || d.Advice[0].Kind != diagnostic.AdviceHelp {
		t.Fatalf("expected actionable help, got %#v", d.Advice)
	}
}
