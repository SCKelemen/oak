package nativegen

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
)

func cleanupText(t *testing.T, body string) (string, int) {
	t.Helper()
	unit, errs := asm.ParseUnit("c.oakasm", "f: (a: u32, b: u32) -> u32 = {\n  bind w0 = a\n  bind w1 = b\n  clobber w9, w10, w19\n"+body+"\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	items, n := cleanupItems(unit.Functions[0].Items)
	fn := *unit.Functions[0]
	fn.Items = items
	return Describe(&fn), n
}

// The late cleanup (nativegen/cleanup.go): a copy read once by the next
// instruction is forwarded, a definition copied once writes its
// destination, a branch to the following label goes, and a copy whose
// value is read again stays.
func TestCleanupCopies(t *testing.T) {
	// Rule 1: the copy feeds one compare-and-branch.
	out, n := cleanupText(t, "  mov w10, w1\n  cbz w10, zero\n  mov w0, w0\n  ret\nzero:\n  movz w0, #7\n  ret")
	if n != 2 || !strings.Contains(out, "cbz w1, zero") || strings.Contains(out, "mov w10, w1") || strings.Contains(out, "mov w0, w0") {
		t.Fatalf("the copy must be forwarded into cbz and the self-move dropped (%d removed):\n%s", n, out)
	}
	// Rule 1 does not fire when the copy is read again.
	out, n = cleanupText(t, "  mov w10, w1\n  add w9, w10, #1\n  add w0, w9, w10\n  ret")
	if n != 0 || !strings.Contains(out, "mov w10, w1") {
		t.Fatalf("a copy read twice must stay (%d removed):\n%s", n, out)
	}
	// Rule 1 does not fire across a W copy read as X.
	out, n = cleanupText(t, "  mov w10, w1\n  add x0, x10, #1\n  ret")
	if n != 0 {
		t.Fatalf("a W copy read at X width must stay (%d removed):\n%s", n, out)
	}
	// Rule 2: a definition copied once writes its destination.
	out, n = cleanupText(t, "  movz w10, #1\n  mov w9, w10\n  add w0, w9, w1\n  ret")
	if n != 1 || !strings.Contains(out, "movz w9, #1") || strings.Contains(out, "mov w9, w10") {
		t.Fatalf("the constant must land in its destination (%d removed):\n%s", n, out)
	}
	// Rule 2 does not fire when the source is read afterwards; rule 1
	// forwards the copy into its one reader instead.
	out, n = cleanupText(t, "  movz w10, #1\n  mov w9, w10\n  add w0, w9, w10\n  ret")
	if n != 1 || !strings.Contains(out, "movz w10, #1") || !strings.Contains(out, "add w0, w10, w10") {
		t.Fatalf("the definition must stay and its copy forward into the add (%d removed):\n%s", n, out)
	}
	// Rule 3: a branch to the next label.
	out, n = cleanupText(t, "  cbz w0, else\n  movz w9, #1\n  b endif\nelse:\n  movz w9, #2\n  b endif\nendif:\n  mov w0, w9\n  ret")
	if n != 1 || strings.Count(out, "b endif") != 1 {
		t.Fatalf("the branch to the following label must go (%d removed):\n%s", n, out)
	}
	// A copy live across a join stays: both arms write the scratch, the
	// join reads it.
	out, n = cleanupText(t, "  cbz w0, else\n  mov w9, w1\n  b endif\nelse:\n  mov w9, w0\nendif:\n  mov w0, w9\n  ret")
	if strings.Contains(out, "mov w0, w1") {
		t.Fatalf("a copy read after a join must not be forwarded:\n%s", out)
	}
	// A call reads its argument registers implicitly: the copy stays.
	out, n = cleanupText(t, "  mov w0, w1\n  bl g\n  ret")
	if n != 0 {
		t.Fatalf("an argument copy before a call must stay (%d removed):\n%s", n, out)
	}
}
