package borrowchecker

import "testing"

// Implementation tests for docs/spec/50-borrowing.md section 5 (Oak.Escape):
// a borrow may not outlive the owner that proves its lifetime, so returning a
// view or span from a function is rejected (OAK-B0109) until region-indexed
// signatures exist to prove the owner outlives the call.

func TestFunctionReturningViewReportsEscape(t *testing.T) {
	bc, program, tc := setupBorrowCheckerForTest("fn dangle(buf: [16]u8) -> []u8 { buf[0:8] }")
	if program == nil {
		t.Fatal("failed to parse view-returning function")
	}
	bc.CheckProgram(program, tc.Env())
	if got := countDiagnosticsWithCode(bc, string(CodeBorrowEscape)); got != 1 {
		t.Fatalf("view-returning function produced %d %s diagnostics, want exactly 1: %#v",
			got, CodeBorrowEscape, bc.Diagnostics())
	}
}

func TestFunctionReturningSpanReportsEscape(t *testing.T) {
	bc, program, tc := setupBorrowCheckerForTest("fn dangle(buf: [16]u8) -> [*]u8 { span(&buf) }")
	if program == nil {
		t.Fatal("failed to parse span-returning function")
	}
	bc.CheckProgram(program, tc.Env())
	if got := countDiagnosticsWithCode(bc, string(CodeBorrowEscape)); got != 1 {
		t.Fatalf("span-returning function produced %d %s diagnostics, want exactly 1: %#v",
			got, CodeBorrowEscape, bc.Diagnostics())
	}
}

func TestFunctionReturningOwnedValueWithInternalBorrowIsClean(t *testing.T) {
	bc, program, tc := setupBorrowCheckerForTest("fn first(buf: [16]u8) -> u8 { v: []u8 = buf[0:8]\nbuf[0] }")
	if program == nil {
		t.Fatal("failed to parse owned-returning function")
	}
	bc.CheckProgram(program, tc.Env())
	if len(bc.Diagnostics()) != 0 {
		t.Fatalf("owned-returning function with internal borrow must be clean, got %#v", bc.Diagnostics())
	}
}

// Function block bodies retain every statement, so borrow conflicts inside
// them are detected (they were previously invisible to the checker).
func TestBorrowConflictInsideBlockBodyIsDetected(t *testing.T) {
	bc, program, tc := setupBorrowCheckerForTest(
		"fn bad(buf: [16]u8) -> u8 { s: [*]u8 = span(&buf)\nv: []u8 = buf[0:4]\nbuf[0] }")
	if program == nil {
		t.Fatal("failed to parse conflicting-body function")
	}
	bc.CheckProgram(program, tc.Env())
	if got := countDiagnosticsWithCode(bc, string(CodeViewConflictsWithSpan)); got == 0 {
		t.Fatalf("view/span conflict inside a block body went undetected: %#v", bc.Diagnostics())
	}
	if got := countDiagnosticsWithCode(bc, string(CodeBorrowEscape)); got != 0 {
		t.Fatalf("owned return type must not report escape, got %d: %#v", got, bc.Diagnostics())
	}
}

// Borrows created inside a function body do not leak into the enclosing scope.
func TestFunctionLocalBorrowsAreDroppedAtFunctionEnd(t *testing.T) {
	bc, program, tc := setupBorrowCheckerForTest(
		"fn f(buf: [16]u8) -> u8 { s: [*]u8 = span(&buf)\ns[0] }\nouter: [16]u8\nw: [*]u8 = span(&outer)")
	if program == nil {
		t.Fatal("failed to parse program with function and outer borrow")
	}
	bc.CheckProgram(program, tc.Env())
	if len(bc.Diagnostics()) != 0 {
		t.Fatalf("function-local borrows leaked into the outer scope: %#v", bc.Diagnostics())
	}
}
