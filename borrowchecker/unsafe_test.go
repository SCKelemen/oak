package borrowchecker

import (
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// Implementation tests for the unsafe boundary (Oak.Unsafe, docs/spec
// 00-constitution and 50-borrowing section 6): unsafe admits exactly the
// writable-disjointness assumption, records every admission as an auditable
// warning, keeps all unrelated checks, and scopes the admission lexically.

func countBySeverity(bc *BorrowChecker, severity diagnostic.DiagnosticSeverity) int {
	count := 0
	for _, d := range bc.Diagnostics() {
		if d.Severity == severity {
			count++
		}
	}
	return count
}

func TestUnsafeAdmitsUnprovableSpanOverlapAsWarning(t *testing.T) {
	bc, program, tc := setupBorrowCheckerForTest(
		"buf: [16]u8\nunsafe {\na: [*]u8 = span(&buf)\nb: [*]u8 = span(&buf)\n}")
	if program == nil {
		t.Fatal("failed to parse unsafe span program")
	}
	bc.CheckProgram(program, tc.Env())
	if got := countBySeverity(bc, diagnostic.SeverityError); got != 0 {
		t.Fatalf("unsafe-admitted overlap produced %d errors, want 0: %#v", got, bc.Errors())
	}
	if got := countDiagnosticsWithCode(bc, string(CodeUnsafeAssumption)); got != 1 {
		t.Fatalf("unsafe admission produced %d %s records, want exactly 1: %#v",
			got, CodeUnsafeAssumption, bc.Diagnostics())
	}
	if got := countBySeverity(bc, diagnostic.SeverityWarning); got != 1 {
		t.Fatalf("unsafe admission must be a warning, got %d warnings", got)
	}
}

func TestSpanOverlapOutsideUnsafeRemainsAnError(t *testing.T) {
	bc, program, tc := setupBorrowCheckerForTest(
		"buf: [16]u8\na: [*]u8 = span(&buf)\nb: [*]u8 = span(&buf)")
	if program == nil {
		t.Fatal("failed to parse overlapping span program")
	}
	bc.CheckProgram(program, tc.Env())
	if got := countDiagnosticsWithCode(bc, string(CodeSpanOverlap)); got != 1 {
		t.Fatalf("safe-code overlap produced %d %s diagnostics, want exactly 1: %#v",
			got, CodeSpanOverlap, bc.Diagnostics())
	}
	if got := countDiagnosticsWithCode(bc, string(CodeUnsafeAssumption)); got != 0 {
		t.Fatalf("safe code must not record unsafe assumptions, got %d", got)
	}
}

func TestUnsafeAdmitsOverlappingReborrowAsWarning(t *testing.T) {
	bc, program, tc := setupBorrowCheckerForTest(
		"buf: [16]u8\nparent: [*]u8 = span(&buf)\nunsafe {\nleft: [*]u8 = parent[0:8]\nmid: [*]u8 = parent[4:12]\n}")
	if program == nil {
		t.Fatal("failed to parse unsafe reborrow program")
	}
	bc.CheckProgram(program, tc.Env())
	if got := countBySeverity(bc, diagnostic.SeverityError); got != 0 {
		t.Fatalf("unsafe-admitted reborrow produced %d errors, want 0: %#v", got, bc.Errors())
	}
	if got := countDiagnosticsWithCode(bc, string(CodeUnsafeAssumption)); got != 1 {
		t.Fatalf("unsafe reborrow admission produced %d %s records, want exactly 1: %#v",
			got, CodeUnsafeAssumption, bc.Diagnostics())
	}
}

// Unsafe admits only the disjointness obligation: view/span exclusivity is
// an unrelated invariant and remains a hard error inside unsafe.
func TestUnsafeKeepsViewSpanExclusivity(t *testing.T) {
	bc, program, tc := setupBorrowCheckerForTest(
		"buf: [16]u8\nunsafe {\ns: [*]u8 = span(&buf)\nv: []u8 = buf[0:4]\n}")
	if program == nil {
		t.Fatal("failed to parse unsafe exclusivity program")
	}
	bc.CheckProgram(program, tc.Env())
	if got := countDiagnosticsWithCode(bc, string(CodeViewConflictsWithSpan)); got != 1 {
		t.Fatalf("view/span exclusivity inside unsafe produced %d %s diagnostics, want exactly 1: %#v",
			got, CodeViewConflictsWithSpan, bc.Diagnostics())
	}
}

// The admission is lexically scoped: after the unsafe block ends, unprovable
// disjointness is rejected again.
func TestUnsafeAssumptionDoesNotOutliveTheBlock(t *testing.T) {
	bc, program, tc := setupBorrowCheckerForTest(
		"buf: [16]u8\nunsafe {\na: [*]u8 = span(&buf)\n}\nb: [*]u8 = span(&buf)\nc: [*]u8 = span(&buf)")
	if program == nil {
		t.Fatal("failed to parse scoped unsafe program")
	}
	bc.CheckProgram(program, tc.Env())
	if got := countDiagnosticsWithCode(bc, string(CodeSpanOverlap)); got != 1 {
		t.Fatalf("overlap after the unsafe block produced %d %s diagnostics, want exactly 1: %#v",
			got, CodeSpanOverlap, bc.Diagnostics())
	}
	if got := countDiagnosticsWithCode(bc, string(CodeUnsafeAssumption)); got != 0 {
		t.Fatalf("no assumption should be recorded outside unsafe, got %d", got)
	}
}
