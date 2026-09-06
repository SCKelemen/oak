package compiler

import (
	"errors"
	"testing"

	"github.com/SCKelemen/oak/typechecker"
)

func TestCheckPreservesStructuredTypeDiagnostics(t *testing.T) {
	input := `
Position: type = { x: i32, y: i32 }
Point1: type = struct { x: i32 }
fn [T: Position] sum_xy(p: T) -> i32 { p.x + p.y }
p: Point1 = Point1 { x: 1 }
result: i32 = sum_xy(p)
`

	_, err := New().WithSource("shape.oak", input).Check().Get()
	if err == nil {
		t.Fatal("expected typecheck failure")
	}

	var diagnosticErr *DiagnosticError
	if !errors.As(err, &diagnosticErr) {
		t.Fatalf("expected *DiagnosticError, got %T: %v", err, err)
	}
	if diagnosticErr.Phase != "typecheck" {
		t.Fatalf("expected typecheck phase, got %q", diagnosticErr.Phase)
	}

	found := false
	for _, d := range diagnosticErr.Diagnostics {
		if d.Code == typechecker.CodeConstraintUnsatisfied {
			found = true
			if err := d.Validate(); err != nil {
				t.Fatalf("structured diagnostic invalid: %v", err)
			}
		}
	}
	if !found {
		t.Fatalf("expected %s in %#v", typechecker.CodeConstraintUnsatisfied, diagnosticErr.Diagnostics)
	}
}
