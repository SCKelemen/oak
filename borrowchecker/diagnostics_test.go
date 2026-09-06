package borrowchecker

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/token"
)

func diagnosticIdent(name string, line, column int) *ast.Identifier {
	return &ast.Identifier{
		Token: token.Token{
			TokenKind: token.IDENT,
			Literal:   name,
			Line:      line,
			Column:    column,
			EndLine:   line,
			EndColumn: column + len(name),
		},
		Value: name,
	}
}

func findBorrowDiagnostic(t *testing.T, bc *BorrowChecker, code diagnostic.Code) *diagnostic.Diagnostic {
	t.Helper()
	for _, d := range bc.Diagnostics() {
		if d.Code == string(code) {
			return d
		}
	}
	t.Fatalf("expected diagnostic %s, got %#v", code, bc.Diagnostics())
	return nil
}

func hasAdviceKind(d *diagnostic.Diagnostic, kind diagnostic.AdviceKind) bool {
	for _, advice := range d.Advice {
		if advice.Kind == kind {
			return true
		}
	}
	return false
}

func TestViewConflictPointsToExistingWritableSpan(t *testing.T) {
	bc := New()
	bc.ownerStates["buf"] = UniqueWrite
	bc.activeBorrows["writer"] = borrowInfo{
		owner:  "buf",
		kind:   BorrowSpan,
		region: &Region{Offset: 0, Length: 16},
		origin: diagnosticIdent("writer", 2, 3),
	}

	bc.createViewBorrowWithRegion(
		"buf",
		"reader",
		&Region{Offset: 0, Length: 8},
		diagnosticIdent("reader", 4, 5),
	)

	d := findBorrowDiagnostic(t, bc, CodeViewConflictsWithSpan)
	if d.Category != diagnostic.CategoryBorrow {
		t.Fatalf("expected borrow category, got %q", d.Category)
	}
	if err := d.Validate(); err != nil {
		t.Fatalf("diagnostic is not structurally valid: %v", err)
	}
	if len(d.Labels) != 2 || d.Labels[0].Style != diagnostic.LabelPrimary || d.Labels[1].Style != diagnostic.LabelSecondary {
		t.Fatalf("expected primary request plus secondary existing borrow, got %#v", d.Labels)
	}
	if !strings.Contains(d.Labels[1].Message, "writer") {
		t.Fatalf("secondary label should name existing span, got %q", d.Labels[1].Message)
	}
	if !hasAdviceKind(d, diagnostic.AdviceHelp) {
		t.Fatalf("expected actionable help, got %#v", d.Advice)
	}
}

func TestSpanOverlapReportsDeterministicConflictingBorrowAndRegions(t *testing.T) {
	bc := New()
	bc.ownerStates["buf"] = UniqueWrite
	bc.activeBorrows["zeta"] = borrowInfo{
		owner:  "buf",
		kind:   BorrowSpan,
		region: &Region{Offset: 0, Length: 12},
		origin: diagnosticIdent("zeta", 2, 1),
	}
	bc.activeBorrows["alpha"] = borrowInfo{
		owner:  "buf",
		kind:   BorrowSpan,
		region: &Region{Offset: 4, Length: 8},
		origin: diagnosticIdent("alpha", 3, 1),
	}

	bc.createSpanBorrowWithRegion(
		"buf",
		"next",
		&Region{Offset: 6, Length: 4},
		diagnosticIdent("next", 5, 1),
	)

	d := findBorrowDiagnostic(t, bc, CodeSpanOverlap)
	if len(d.Labels) != 2 {
		t.Fatalf("expected new span and one causal existing span, got %#v", d.Labels)
	}
	// activeBorrowNames sorts names, so diagnostics do not depend on Go map order.
	if !strings.Contains(d.Labels[1].Message, "alpha") {
		t.Fatalf("expected deterministic first conflict alpha, got %q", d.Labels[1].Message)
	}
	joined := d.PlainText()
	if !strings.Contains(joined, "[6..10)") || !strings.Contains(joined, "[4..12)") {
		t.Fatalf("diagnostic should explain both regions, got %q", joined)
	}
}

func TestUnknownSpanRegionFailsClosedAndExplainsWhy(t *testing.T) {
	bc := New()
	bc.ownerStates["buf"] = UniqueWrite
	bc.activeBorrows["left"] = borrowInfo{
		owner:  "buf",
		kind:   BorrowSpan,
		region: &Region{Offset: 0, Length: 8},
		origin: diagnosticIdent("left", 2, 1),
	}

	bc.createSpanBorrowWithRegion("buf", "dynamic", nil, diagnosticIdent("dynamic", 4, 1))

	d := findBorrowDiagnostic(t, bc, CodeSpanOverlap)
	if !strings.Contains(d.PlainText(), "could not prove") {
		t.Fatalf("unknown-region rejection should explain conservative proof failure, got %q", d.PlainText())
	}
}

func TestOwnerWriteDuringViewPointsBackToView(t *testing.T) {
	bc := New()
	bc.ownerStates["buf"] = SharedRead
	bc.activeBorrows["header"] = borrowInfo{
		owner:  "buf",
		kind:   BorrowView,
		region: &Region{Offset: 0, Length: 4},
		origin: diagnosticIdent("header", 2, 1),
	}

	bc.checkIdentifierUse(diagnosticIdent("buf", 5, 1), "buf", nil, true)

	d := findBorrowDiagnostic(t, bc, CodeOwnerWrittenDuringView)
	if len(d.Labels) != 2 || !strings.Contains(d.Labels[1].Message, "header") {
		t.Fatalf("expected causal view label, got %#v", d.Labels)
	}
	if !hasAdviceKind(d, diagnostic.AdviceHelp) {
		t.Fatal("expected safe remediation help")
	}
}

func TestDisjointWritableSpansRemainAllowed(t *testing.T) {
	bc := New()
	bc.ownerStates["buf"] = UniqueWrite
	bc.activeBorrows["left"] = borrowInfo{
		owner:  "buf",
		kind:   BorrowSpan,
		region: &Region{Offset: 0, Length: 8},
		origin: diagnosticIdent("left", 2, 1),
	}

	bc.createSpanBorrowWithRegion(
		"buf",
		"right",
		&Region{Offset: 8, Length: 8},
		diagnosticIdent("right", 3, 1),
	)

	if got := bc.Diagnostics(); len(got) != 0 {
		t.Fatalf("disjoint spans should not produce diagnostics: %#v", got)
	}
	if _, ok := bc.activeBorrows["right"]; !ok {
		t.Fatal("disjoint span should have been registered")
	}
}

func TestErrorsIsCompatibilityProjectionOfDiagnostics(t *testing.T) {
	bc := New()
	bc.ownerStates["buf"] = SharedRead
	bc.activeBorrows["view"] = borrowInfo{owner: "buf", kind: BorrowView}
	bc.checkIdentifierUse(diagnosticIdent("buf", 1, 1), "buf", nil, true)

	errs := bc.Errors()
	if len(errs) != 1 || !strings.Contains(errs[0], string(CodeOwnerWrittenDuringView)) {
		t.Fatalf("expected stable diagnostic code in compatibility output, got %#v", errs)
	}
}
