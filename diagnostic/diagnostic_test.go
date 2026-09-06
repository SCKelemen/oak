package diagnostic

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/lsp"
)

func testRange(line, start, end int) lsp.Range {
	return lsp.Range{
		Start: lsp.Position{Line: line, Character: start},
		End:   lsp.Position{Line: line, Character: end},
	}
}

func TestDiagnosticConstructorProvidesStableCodeAndPrimaryLabel(t *testing.T) {
	rng := testRange(2, 4, 7)
	d := NewDiagnostic(rng, "typechecker", "undefined variable `foo`")

	if d.Code != string(CodeTypeGeneric) {
		t.Fatalf("expected %s, got %s", CodeTypeGeneric, d.Code)
	}
	if d.Category != CategoryType {
		t.Fatalf("expected type category, got %q", d.Category)
	}
	if d.Title != "undefined variable `foo`" || d.Message != d.Title {
		t.Fatalf("title/message compatibility not preserved: %#v", d)
	}
	if len(d.Labels) != 1 || d.Labels[0].Style != LabelPrimary || d.Labels[0].Range != rng {
		t.Fatalf("expected one primary label at diagnostic range, got %#v", d.Labels)
	}
	if err := d.Validate(); err != nil {
		t.Fatalf("new diagnostic should be well formed: %v", err)
	}
}

func TestDiagnosticSupportsSecondaryContextNotesAndHelp(t *testing.T) {
	primary := testRange(1, 3, 8)
	secondary := testRange(0, 0, 5)
	d := NewDiagnosticWithCode(primary, "borrow", "OAK-B0001", "view escapes its backing storage")
	d.SetPrimary(primary, "returned view escapes here")
	d.AddSecondary(secondary, "backing storage ends here")
	d.AddNote("the view does not own the referenced bytes")
	d.AddHelp("return an owned value or keep the backing storage alive")

	if err := d.Validate(); err != nil {
		t.Fatalf("structured diagnostic should be well formed: %v", err)
	}

	text := d.PlainText()
	for _, want := range []string{
		"error[OAK-B0001]: view escapes its backing storage",
		"primary: returned view escapes here",
		"secondary: backing storage ends here",
		"note: the view does not own the referenced bytes",
		"help: return an owned value or keep the backing storage alive",
	} {
		if !strings.Contains(text, want) {
			t.Fatalf("PlainText() missing %q:\n%s", want, text)
		}
	}
}

func TestSetPrimaryKeepsExactlyOnePrimary(t *testing.T) {
	d := NewDiagnostic(testRange(0, 0, 1), "parser", "unexpected token")
	d.AddSecondary(testRange(0, 2, 3), "expression started here")
	d.SetPrimary(testRange(1, 4, 5), "parser stopped here")

	primary := 0
	secondary := 0
	for _, label := range d.Labels {
		switch label.Style {
		case LabelPrimary:
			primary++
		case LabelSecondary:
			secondary++
		}
	}
	if primary != 1 || secondary != 1 {
		t.Fatalf("expected one primary and one secondary label, got primary=%d secondary=%d", primary, secondary)
	}
	if err := d.Validate(); err != nil {
		t.Fatalf("diagnostic should remain well formed: %v", err)
	}
}

func TestValidateRejectsMissingStableIdentityOrPrimaryCause(t *testing.T) {
	d := &Diagnostic{Title: "broken", Severity: SeverityError}
	if err := d.Validate(); err == nil {
		t.Fatal("expected missing code to be rejected")
	}

	d.Code = "OAK-I9999"
	if err := d.Validate(); err == nil {
		t.Fatal("expected missing primary label to be rejected")
	}
}
