package nativegen

import (
	"strings"
	"testing"
)

// The walkers' status byte: set to 1, conditionally cleared, compared
// with 1. The clearing path threads past the compare, and the compare,
// left with the one predecessor that knows the register holds 1, goes.
func TestFoldConstantBranchesOnStatusByte(t *testing.T) {
	out, n := cleanupText(t, strings.Join([]string{
		"  movz w4, #1",
		"  cmp x0, x1",
		"  b.lo else_4",
		"  mov w4, wzr",
		"  b endif_5",
		"else_4:",
		"endif_5:",
		"  cmp w4, #1",
		"  b.ne else_6",
		"  add w0, w0, #1",
		"else_6:",
		"  mov w0, w4",
		"  ret",
	}, "\n"))
	if strings.Contains(out, "cmp w4, #1") || !strings.Contains(out, "b else_6") || strings.Contains(out, "b.ne else_6") {
		t.Fatalf("the status compare must fold and its clearing path thread to else_6 (%d removed):\n%s", n, out)
	}
	if !strings.Contains(out, "mov w4, wzr") || !strings.Contains(out, "movz w4, #1") {
		t.Fatalf("the status writes stay, being read at the end:\n%s", out)
	}
	// A merge move at the target travels with the threaded jump.
	out, n = cleanupText(t, strings.Join([]string{
		"  movz w4, #1",
		"  cmp x0, x1",
		"  b.lo else_4",
		"  mov w9, wzr",
		"  b endif_5",
		"else_4:",
		"  mov w9, w4",
		"endif_5:",
		"  mov w4, w9",
		"  cmp w4, #1",
		"  b.ne else_6",
		"  add w0, w0, #1",
		"else_6:",
		"  mov w0, w4",
		"  ret",
	}, "\n"))
	if strings.Contains(out, "cmp w4, #1") || !strings.Contains(out, "b else_6") {
		t.Fatalf("the merge move must travel with the threaded jump (%d removed):\n%s", n, out)
	}
	// On the threaded path w4 must still read 0: the copied merge move or
	// its forwarded form writes w4 before the jump.
	if !strings.Contains(out, "mov w4, wzr") && !strings.Contains(out, "mov w4, w9") {
		t.Fatalf("the threaded path must still clear the status:\n%s", out)
	}
	// A register the predecessors disagree on is not folded.
	out, n = cleanupText(t, "  cbz w0, zero\n  movz w4, #1\n  b join\nzero:\n  movz w4, #2\njoin:\n  cmp w4, #1\n  b.ne other\n  add w0, w0, #1\nother:\n  mov w0, w4\n  ret")
	if !strings.Contains(out, "cmp w4, #1") {
		t.Fatalf("a compare over a register the predecessors disagree on stays (%d removed):\n%s", n, out)
	}
	// A compare whose flags a later select reads stays.
	out, n = cleanupText(t, "  movz w4, #1\n  cmp w4, #1\n  b.ne other\n  csel w0, w1, w2, eq\n  ret\nother:\n  mov w0, w4\n  ret")
	if !strings.Contains(out, "cmp w4, #1") {
		t.Fatalf("a compare whose flags are read stays (%d removed):\n%s", n, out)
	}
	// A call forgets the caller-saved registers.
	out, n = cleanupText(t, "  movz w9, #1\n  bl f\n  cmp w9, #1\n  b.ne other\n  add w0, w0, #1\nother:\n  ret")
	if !strings.Contains(out, "cmp w9, #1") {
		t.Fatalf("a compare after a call stays (%d removed):\n%s", n, out)
	}
}
